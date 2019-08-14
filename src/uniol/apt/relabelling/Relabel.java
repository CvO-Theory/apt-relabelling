/*-
 * APT - Analysis of Petri Nets and labeled Transition systems
 * Copyright (C) 2012-2013  Members of the project group APT
 * Copyright (C) 2014-2019  Parallel System Group, University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

package uniol.apt.relabelling;

import java.util.HashSet;
import java.util.Set;
import java.util.HashMap;
import java.util.TreeMap;
import java.util.Map;
import java.util.Iterator;
import java.util.Deque;
import java.util.LinkedList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;
import java.math.BigInteger;
import java.util.Stack;
import java.util.Collection;

import uniol.apt.adt.pn.PetriNet;
import uniol.apt.adt.pn.Marking;
import uniol.apt.adt.pn.Place;
import uniol.apt.adt.ts.Arc;
import uniol.apt.adt.ts.State;
import uniol.apt.adt.ts.TransitionSystem;
import uniol.apt.analysis.synthesize.PNProperties;
//import uniol.apt.analysis.synthesize.LimitedUnfolding;
//import uniol.apt.analysis.exception.NonDeterministicException;
import uniol.apt.util.interrupt.InterrupterRegistry;
import uniol.apt.util.equations.InequalitySystem;
import uniol.apt.util.equations.InequalitySystemSolver;

/**
 * Relabel an LTS so it becomes PN solvable
 *
 * @author Harro Wimmel
 *
 */
public class Relabel {

	// the input lts
	private final TransitionSystem ts;

	// the number of states in the lts
	private int numnodes;
	// local representation of the lts with additional data stuctures
	private SNode[] nodes;
	// a map from APT states to local IDs (index in the above array)
	private Map<State,Integer> id;

	// the result of the overall operation
	boolean result = true;
	// the quick-fail option
	boolean qf;
	// the SSP option
	boolean ssp;
	// the ESSP option
	boolean essp;

	// three lists representing state/label/state info of chords
	private ArrayList<Integer> chsource;
	private ArrayList<Integer> chlabel;
	private ArrayList<Integer> chsink;
	// additionally, we mark renamed chords, so they will not be used for the cyclebasis
	private ArrayList<Boolean> chrenamed;

	// a list of parikh vectors of the cyclebasis with the chords associated to each vector
	private ArrayList<Map<Integer,Integer>> cyclebasis;
	private ArrayList<Set<Integer>> chordbasis;
	// vectors in cyclebasis can be linearly dependent, for an independent subset (indices of cyclebasis) we use:
	private ArrayList<Integer> truecyclebasis;

	// a list of sets of parikh equivalent states after ESSP are solved, starting with minimal depth
	private ArrayList<Set<Integer>> peqlist;
	// map of relabellings for parikh equivalent states so far, from new to old labels
	private Map<Integer,Integer> relabelling;

	// the size of the alphabet of ts. This will change when new
	// labels are created
	private int alphabetsize;

	// a mapping from the label strings of APT to their internal ID
	private Map<String,Integer> label2id;
	// a mapping from the internal label IDs to the label strings
	private ArrayList<String> id2label;
	// if label x is created as a renaming of label y, labelref.get(x)=y
	// otherwise if label x is original, the mapping contains -1 as value
	private ArrayList<Integer> labelref;
	// for each label x, enabled.get(x) contains all states that allow
	// an edge with label x
	private Map<Integer,Set<Integer>> enabled;
	// for each original label all IDs of its copies, including itself
	private Map<Integer,ArrayList<Integer>> label_copies;

	/**
	 * Creates a new {@link Relabel} instance that operates on the
	 * given transition system.
	 *
	 * @param ts The transition system to relabel
	 * @param qf If a quick-fail mechanism should be applied
	 */
	public Relabel(TransitionSystem ts, PNProperties prop, boolean qf, boolean ssp, boolean essp, boolean time, boolean delayssp, boolean truebase, boolean shallowtree) {
		// we want to measure the time
		long time1, time2;
		time1 = System.currentTimeMillis();
		// make a copy of the transition system since we will modify it
		this.ts = new TransitionSystem(ts);
		this.ts.setName("Relabelled "+ts.getName());
		// quick-fail option
		this.qf = qf;
		// the size of ts' alphabet, may be enlarged later
		alphabetsize = ts.getAlphabet().size();
		// mapping from labels to the set of states enabling it
		enabled = new HashMap<Integer,Set<Integer>>();
		// translation of labels to integers and handling of modified copies of labels
		label2id = new HashMap<String,Integer>();
		id2label = new ArrayList<String>();
		labelref = new ArrayList<Integer>();
		label_copies = new HashMap<Integer,ArrayList<Integer>>();
		int id = 0;
		for (String lab : ts.getAlphabet()) {
			enabled.put(id,new HashSet<Integer>());
			ArrayList<Integer> tmp = new ArrayList<Integer>();
			tmp.add(id);
			label_copies.put(id,tmp);
			label2id.put(lab,id++);
			id2label.add(lab);
			labelref.add(-1);
		}

		// the list of all chords of ts
		chsource = new ArrayList<Integer>();
		chlabel = new ArrayList<Integer>();
		chsink = new ArrayList<Integer>();
		// if the chord has already been renamed (it then has a worthless cycle)
		chrenamed = new ArrayList<Boolean>();

		// the cycle basis, computed from the chords
		cyclebasis = new ArrayList<Map<Integer,Integer>>();
		// for each cycle of the basis, a set of chords belonging to the cycle
		chordbasis = new ArrayList<Set<Integer>>();
		truecyclebasis = new ArrayList<Integer>();

		// first construct a breadth-first spanning tree and
		// detect some basic properties while at it
		int lastnode = spanningTree(shallowtree);
		if (lastnode < numnodes) result = false;
		if (qf && !result) return;

		// for simple SSP (not involving cycles) we remember fro each new label the original one
		relabelling = new HashMap<Integer,Integer>();

		// first solve SSP where states have the same Parikh vector
		if (ssp) checkSimpleSSP();

		// compute the cycle basis (will be recomputed often, later)
		if (ssp || essp) cycleBasis();

		// should we delay SSPs or just do all ESSPs at the end?
		if (delayssp) {
			// now solve all ESSP so far
			if (essp) checkESSP(0,truebase);

			// finally solve SSP where the difference of two states can be bridged by the cycle basis
			if (ssp) {
				int maxlab = id2label.size();
				checkCyclicSSP(truebase);
				// as there may be multiply used new labels, we need to solve ESSP for these
				if (essp) checkESSP(maxlab,truebase);
			}
		} else {
			if (ssp) checkCyclicSSP(truebase);
			if (essp) checkESSP(0,truebase);
		}

		// measure time
		time2 = System.currentTimeMillis();
		if (time) System.err.println(""+(time2-time1)+" ms");
	}

	/**
	 * Check all ESSP starting with a given label
	 *
	 * @param start The ID of the label to start at, all higher IDs will also be considered
	 */
	private void checkESSP(int start, boolean basetransform) {
		// we go through the labels one by one, new labels will be appended
		// at the end of our to-do-list
		int lnum = start, newnum = 0;
		// for the linear inequation systems we need to know which
		// variable belongs to which state in the TS
		ArrayList<Integer> statevars = new ArrayList<Integer>();

		// now we start our loop and go on as long as there are unprocessed labels
		// (original ones or those newly created)
		while (lnum < id2label.size()) {
			// we only create at most one new label in one go
			// so we need to remember if we have already created one
			boolean new_label = false;
			int last_label = -1;
			// obtain all states allowing this label
			Set<Integer> enabled_states = enabled.get(lnum);
			for (int st=0; st<numnodes; st++) {
				// we are interested in states NOT allowing the label
				if (enabled_states.contains(st)) continue;
				// clear the variable-to-state connection
				statevars.clear();
				// build a new inequality system with rational variables
				RationalSystemSolver rss = new RationalSystemSolver();
				truecyclebasis.clear();
				if (basetransform) trueCycleBasis(new BaseTransform(alphabetsize));
				rss.assertDisjunction(buildESSPDualSystem(st,lnum,statevars));
				// check if the system has a solution, if not, the ESSP is solvable and we are done
				List<BigInteger> solution = rss.findSolution();
				if (solution.isEmpty()) continue;

				// if so, we need to rename some label
				// we find the state with the best contribution to the solution
				int maxstate = findMaxStateVar(solution,statevars);
				// in case there is only one state at all we get the 2' complement of it
				if (maxstate<0) {
					maxstate = -maxstate-1;
					// this means we need to fix a cycle contributing to the solution
					int cycle = findBestCycle(solution,statevars);
					// if we find one we choose the best and fix it
					if (cycle >= 0) modifyCycle(cycle, st, maxstate);
					// otherwise we have a simple SSP, which we solve now in case of ESSP-only
					else modifySpan(st, maxstate, lnum, (new_label ? alphabetsize-1 : -1));
					cycleBasis();
					// since we changed the situation we need to recheck this state
					st--;
					continue;
				}

				// in case this is the first renaming for this label, we need to create a new one
				if (!new_label) { newnum = createLabel(lnum); new_label = true; last_label = newnum;
//					System.out.println("NEWLABEL "+id2label.get(lnum)+" to "+id2label.get(newnum));
				}
				else { newnum = last_label;
//					System.out.println("OLDLABEL "+id2label.get(lnum)+" to "+id2label.get(newnum));
				}
				// we replace the edge labelled lnum at the state maxstate
				// by an edge with the new label
				if (!nodes[maxstate].relabelEdge(lnum,newnum)) {
					System.out.println("Relabel failure "+id2label.get(lnum)+" to "+id2label.get(newnum));
					System.out.print("State "+nodes[maxstate].s.getId());
					for(Map.Entry<Integer,Integer> me : nodes[maxstate].edges.entrySet()) {
						System.out.print(" -"+id2label.get(me.getKey())+"->"+nodes[me.getValue()].s.getId());
					}
					System.out.println();
				}
				// since the renamed edge might appear in a cycle,
				// we must recompute the cycle basis
				cycleBasis();
				// and since we modified an edge we need to recheck this state
				st--;
			}
			// when we are through with all states not allowing the edge with label lnum,
			// we can move on to the next label
			lnum++;
		}
	}

	/**
	 * Check all SSP that connect states through a linear combination of the cycle basis
	 */
	private void checkCyclicSSP(boolean basetransform) {
		// special case of no labels or no cycles
		if (id2label.size()==0 || cyclebasis.isEmpty()) return;
		// Get a base transformation object
		BaseTransform bt = null;
		if (basetransform) bt = new BaseTransform(alphabetsize);
		// we compute an initial semi-equivalence, i.e. states in different classes are not equivalent
		Deque<Set<Integer>> classes = initEquivalence();
		// we make pairwise comparisons inside each class
		for (Set<Integer> tmp : classes) {
			// an array of processed states, these must be compared with each new one
			ArrayList<Integer> inequiv = new ArrayList<Integer>(tmp.size());
			// the first state for the comparison
			for (int state1 : tmp) {
				// the second state for the comparison
				for (int state2 : inequiv)
					// check if there is an unsolvable SSP here and fix it
					if (solveCyclicSSP(state1,state2,bt)) {
						// if there are no more cycles available, we can stop
						if (cyclebasis.isEmpty()) return;
						break; // break due to transitivity
					}
				// mark the first state as processed
				inequiv.add(state1);
			}
		}
	}

	/**
	 * Get an initial equivalence with one class containing all states, or (if ESSP are solved) with one class
	 * per possible set of enabled events.
	 *
	 * @return The equivalence
	 */
	private Deque<Set<Integer>> initEquivalence() {
		// first, we let all states be equivalent
		Deque<Set<Integer>> cyclicEQ = new LinkedList<Set<Integer>>();
		Set<Integer> tmp = new HashSet<Integer>();
		for(int i = 0; i < numnodes; i++) tmp.add(i);
		cyclicEQ.offerLast(tmp);
		// in case we have solved all ESSP, we can split classes according to enabled labels
		if (essp) for(int lab = 0; lab < id2label.size(); lab++) 
			splitEquivalence(cyclicEQ, enabled.get(lab));
		return cyclicEQ;
	}

/*
	private void printEq(Collection<Set<Integer>> classes) {
		for (Set<Integer> test : classes) {
			System.out.print("[");
			printSet(test);
			System.out.print("]");
		}
	}

	private void printSet(Set<Integer> myset) {
			boolean comma = false;
			for (int st1 : myset) {
				if (comma) System.out.print(",");
				System.out.print(nodes[st1].s.getId());
				comma = true;
			}
	}
*/

	/**
	 * Split the classes of an equivalence according to a divider set
	 *
	 * @param classes The equivalence to split, each class may be split in two (or possibly not)
	 * @param divider Each class is split such that all states in divider end up in one new class
	 *		  and the other states in the second new class
	 */
	private void splitEquivalence(Deque<Set<Integer>> classes, Set<Integer> divider) {
		// for termination we need to know the a-priori number of classes
		int size = classes.size();
		// go through the original classes only
		for (int i=0; i<size; i++) {
			Set<Integer> tmp1 = classes.pollFirst();
			Set<Integer> tmp2 = new HashSet<Integer>();
			// remove elements not in divider and put them into a new set
			for (Iterator<Integer> it=tmp1.iterator(); it.hasNext(); ) {
				int state = it.next();
				if (!divider.contains(state)) {
					it.remove();
					tmp2.add(state);
				}
			}
			// append the old (reduced) as well as the new set to the equivalence
			// but only if they contain at least 2 states, meaning that there are
			// indeed SSP to solve
			if (tmp1.size()>1) classes.offerLast(tmp1);
			if (tmp2.size()>1) classes.offerLast(tmp2);
		}
	}

	/**
	 * Solve an SSP where state1 and state2 are connected via a linear combination of the cycle basis
	 *
	 * @param state1 The first state of the SSP
	 * @param state2 The second state of the SSP, must be different
	 * @return If the SSP was unsolvable and thus fixed
	 */
	private boolean solveCyclicSSP(int state1, int state2, BaseTransform bt) {
		// space for a mapping from variables to states/cycles
		ArrayList<Integer> statevars = new ArrayList<Integer>();
		// build a new inequality system with rational variables
		RationalSystemSolver rss = new RationalSystemSolver();
		// compute true cycle basis if desired
		truecyclebasis.clear();
		if (bt != null) trueCycleBasis(bt);
		rss.assertDisjunction(buildSSPDualSystem(state1,state2,statevars));
		// check if the system has a solution
		List<BigInteger> solution = rss.findSolution();
		if (solution.isEmpty()) return false;

		// if there is a solution, i.e. the SSP is unsolvable
		// we look for the best cycle in the basis to modify
		int cycle = findBestCycle(solution,statevars);
		if (cycle >= 0) {
			// we modify the cycle
			modifyCycle(cycle, state1, state2);
			// and exclude it from the cycle basis forever:
			// since the chords got completely new labels, the cycles are unusable
			// for other SSPs
			cyclebasis.remove(cycle);
//System.out.print("REL");
			for (int ch : chordbasis.get(cycle)) {
				chrenamed.set(ch, true);
//				System.out.println(" "+ch);
			}
//System.out.println();
			chordbasis.remove(cycle);
			return true;
		} 
		return false; // cannot happen as simpleSSP have all been fixed before
	}

	/**
	 * Construct a cycle basis in the sense of linear algebra, i.e. with linearly independent vectors
	 * (the normal cycle basis can have linear dependencies)
	 *
	 * @param bt Structure for a base transformation in the linear algebraic sense
	 * @return nothing, result is in truecyclebasis (global)
	 */
	private void trueCycleBasis(BaseTransform bt) {
		int count = alphabetsize;
		for(int i=0; i<cyclebasis.size(); i++)
			if (bt.add(cyclebasis.get(i))) {
				truecyclebasis.add(i);
				if (--count == 0) break;
			}
		bt.clear();
	} 

	/**
	 * Creates a new label as a copy of one old one with a new index
	 *
	 * @param label The old label's ID
	 * @return The new label's ID
	 */
	private int createLabel(int label) {
		int lab = label;
		// first obtain the original ID, note that the label we currently
		// work on may already be a copy. We need to find the original
		while (labelref.get(lab)>=0) lab = labelref.get(lab);
		// add the new label ID to the copy list of the original label
		label_copies.get(lab).add(alphabetsize);
		// now determine the next free index for the new label
		int index = label_copies.get(lab).size();
		// make a reference to the label we work upon
		labelref.add(label);
		// and create a new enabled list for the new label
		enabled.put(alphabetsize,new HashSet<Integer>());
		// finally we set the new string with appended index for this new label
		id2label.add(id2label.get(lab)+"_"+index);
		// and return the new label ID
//System.out.println("CRLAB "+id2label.get(alphabetsize)+" for "+id2label.get(label));
		return alphabetsize++;
	}

	// this class represent a single state with additional data structures for
	// the spanning tree and for solving simple SSP
	// Note that the post edges of the state are copied from the APT structure;
	// changing IDs from String to int.
	private class SNode {

		// the APT state this object represents
		public State s;
		// forward edges to other states, label ID as first parameter, target as second
		// Weak forward determinism is required for this data structure
		public Map<Integer,Integer> edges;
		// the label IDs of all span edges at this state
		public Set<Integer> span;
		// the ID of the father in the spanning tree
		public int father;
		// the label of the edge leading to this state in the spanning tree
		public int span_label;
		// the ID of this state
		public int me;
		// index of the first chord with this state as source in the global chord list
		public int chord_index;
		// distance path Parikh vector (occurrences of labels of the spanning tree path)
		public Map<Integer,Integer> parikh;
		// depth of the state in the spanning tree
		public int depth;
		// index in the peqlist (Parikh-equivalence-list collecting states with the same PV)
		public int peqindex;

		// all data from here is for simple SSP only:
		// map from labels to label sequences on which a renaming is possible/necessary
		public Map<Integer,ArrayList<Integer>> renamingpaths;
		// for simple SSP, which equivalence class uses which labels/edges
		public Map<Integer,Set<Integer>> classlabels;
		// temporary space for the first path in renamingpaths (before it is added)
		public ArrayList<Integer> firstpath;
		// counter for the labels in classlabels
		public Map<Integer,Integer> labelcounter;
		// the next states along the spanning tree where an equivalence class is split
		public Set<Integer> nextbranch;
		// signal that the state should not pass on the firstpath
		public boolean kill;
		// signal the ancestor split state that its renamingpaths must be updated
		public boolean lastkill;
		// if this state occurs in some simple SSP
		public boolean sspstate;
		// the set of new labels occurring in the subtree via some edge (1st parameter)
		public Map<Integer,Set<Integer>> subtreelabels;
		// set of all inheritable labels
		public Set<Integer> inheritablelabels;
		// mapping from labels to which renamingpaths they occur on
		public Map<Integer,Set<Integer>> rpcount;

		/**
		 * Creates a new {@link SNode} instance that represents an APT lts state
		 * with additional data.
		 *
		 * @param t The APT state
		 * @param num The local state ID
		 * @param myfather This node's father in the spanning tree
		 * @param label The edge of the spanning tree from father to this
		 */
		public SNode(State t, int num, int myfather, int label) {
			// data are transferred from parameters
			s = t;
			edges = new HashMap<Integer,Integer>();
			span = new HashSet<Integer>();
			father = myfather;
			span_label = label;
			me = num;
			// most other data structures are initialised, but not all
			chord_index = -1;
			if (father==-1) {
				parikh = new HashMap<Integer,Integer>();
				depth = 0;
			} else {
				depth = nodes[father].depth+1;
				parikh = new HashMap<Integer,Integer>(nodes[father].parikh);
				if (parikh.get(span_label)==null) parikh.put(span_label,1);
				else parikh.put(span_label,parikh.get(span_label)+1);
			}
			peqindex = -1;
			renamingpaths = new HashMap<Integer,ArrayList<Integer>>();
			classlabels = new HashMap<Integer,Set<Integer>>();
			labelcounter = new HashMap<Integer,Integer>();
			nextbranch = new HashSet<Integer>();
			kill = false;
			lastkill = false;
			sspstate = false;
		}

		/**
		 * Add an edge to the internal data structure, i.e. at this state
		 * and add it to the enabled-structure.
		 *
		 * @param label The label of the edge to add (as internal ID)
		 * @param state The ID of the target state
		 * @return If the edge could be created (false = already existent)
		 */
		public boolean createEdge(int label, int state) {
			// check if the edge already exists
			Integer oldstate = edges.get(label);
			if (oldstate != null) return false;
			// set the edge
			edges.put(label,state);
			// check if we are the spanning tree father of 'state'
			if (nodes[state].father == me && nodes[state].span_label == label)
				// set the set of spanning tree labels accordingly
				span.add(label);
			else {
				// otherwise this edge is a chord and we fill those data structures
				if (chord_index == -1) chord_index = chsource.size();
				chsource.add(me);
				chlabel.add(label);
				chsink.add(state);
				chrenamed.add(false);
			}
			// the edge is now enabled at this state
			enabled.get(label).add(me);
			return true;
		}

		/**
		 * Rename an edge in the internal data structure as well as
		 * in the original transition system (for output purposes)
		 *
		 * @param label The label of the edge to rename (as internal ID)
		 * @param newlabel The ID of the new label
		 */
		public boolean relabelEdge(int label, int newlabel) {
			// check that the old label exists but not the new one
			Integer st = edges.get(newlabel);
			if (st != null) return false;
			st = edges.get(label);
			if (st == null) return false;
			edges.remove(label);
			edges.put(newlabel,st);
			// if the edge is part of the spanning tree, we must also
			// change the label there
			if (span.remove(label)) {
				span.add(newlabel);
				nodes[st].span_label = newlabel;
				// modify the Parikh vectors of all successor states
				Stack<Integer> statelist = new Stack<Integer>();
				statelist.push(st);
				while (!statelist.empty()) {
					int state = statelist.pop();
					Map<Integer,Integer> pm = nodes[state].parikh;
					if (pm.put(label,pm.get(label)-1)==1) pm.remove(label);
					Integer i = pm.get(newlabel);
					pm.put(newlabel, (i==null ? 1 : i+1));
					for (int lab : nodes[state].span) 
						statelist.push(nodes[state].edges.get(lab));
			}
			} else if (chord_index >= 0) {
				// update the global chord list
				for (int i = chord_index; chsource.get(i)==me; i++)
					if (chlabel.get(i) == label) {
						chlabel.set(i,newlabel); 
						break; 
					}
			}
			// modify the APT data structure
			modifyTS(label, newlabel, st);
			// the global enabled list must also be adapted
			enabled.get(label).remove(me);
			enabled.get(newlabel).add(me);
			return true;
		}

		/**
		 * Rename an edge in the APT data structure 
		 *
		 * @param oldlabel The label of the edge to rename (as internal ID)
		 * @param newlabel The ID of the new label
		 * @param nextstate The state the edge points to (as internal ID)
		 */
		public void modifyTS(int oldlabel, int newlabel, int nextstate) {
			ts.removeArc(ts.getArc(this.s, nodes[nextstate].s, id2label.get(oldlabel)));
			ts.createArc(this.s, nodes[nextstate].s, id2label.get(newlabel));
		}

		/**
		 * Get all successors of this state in the spanning tree
		 *
		 * @return The set of (direct and transitive) successors
		 */
		private Set<Integer> getSuccessors() {
			// we make a breadth-first search from this state
			Set<Integer> result = new HashSet<Integer>();
			result.add(me);
			// all non-processed states are in todo
			Set<Integer> todo = new HashSet<Integer>();
			todo.add(me);
			while (!todo.isEmpty()) {
				// get one unprocessed state
				int st = todo.iterator().next();
				// and go through its spanning tree edges to add the successors
				for (int lab : nodes[st].span)
					if (result.add(nodes[st].edges.get(lab))) 
						todo.add(nodes[st].edges.get(lab));
				todo.remove(st);
			}
			return result;
		}

	}

	/**
	 * Find the branching point where the spanning tree paths for two states diverge, then
	 * find the first label in a given set on the path from the branching point to the 'left' input state. 
	 *
	 * @param state The input state on the 'left' branch
	 * @param state2 The input state on the 'right' branch
	 * @param labels A set of labels that are preferred; if empty, any label will do
	 * @return The state after the edge with the found, preferred label; 
	 *	if none, the 'left' state after the branching point, or -1 if no true 'left' branch exists.
	 */
	public int branchingPoint(int state, int state2, Set<Integer> labels) {
		int bstate = -1, lstate = -1;
		// to be able to notice a common ancestor, we must bring both states to the same depth first
		while (nodes[state].depth > nodes[state2].depth) {
			// check if we have a preferred label and remember it then
			if (labels.contains(nodes[state].span_label)) lstate = state;
			bstate = state; 
			state = nodes[state].father; 
		}
		while (nodes[state].depth < nodes[state2].depth) state2 = nodes[state2].father;
		// now we are on a common depth and go on synchronously
		while (state != state2) { 
			// remember if we encounter a preferred label
			if (labels.contains(nodes[state].span_label)) lstate = state;
			bstate = state; 
			state = nodes[state].father; 
			state2 = nodes[state2].father; 
		}
		// return a state with preferred label if there is one, any state/label otherwise 
		return (lstate>-1 ? lstate : bstate);
	}

	/**
	 * Determine a replacement label is there are multiple edges with the same label at the same state
	 * (non-determinism). The new label will be the original one plus an index.
	 *
	 * @param label The multiply occurring label
	 * @param multi a map containing the multiplicity of labels
	 * @return The suggested new label (either an existing one or created by this method) 
	 */
	public int determineLabel(int label, Map<Integer,Integer> multi) {
		Integer val = multi.get(label);
		if (val == null) val = 0;
		multi.put(label,val+1);
		if (label_copies.get(label).size() > val)
			return label_copies.get(label).get(val);
		else {
			int newlabel = createLabel(label); 
			label2id.put(id2label.get(newlabel),newlabel);
			return newlabel;
		}
	}



	/**
	 * Construct a breadth-first spanning tree of the lts and
	 * check some local properties.
	 *
	 * @return The number of reachable nodes
	 */
	public int spanningTree(boolean shallowtree) {
		// set number of states overall
		numnodes = ts.getNodes().size();
		// acquire space for all states
		nodes = new SNode[numnodes];
		// for counting all short paths and deciding which edges are in the spanning tree
		BigInteger[] paths = new BigInteger[numnodes];
		BigInteger[] minpaths = new BigInteger[numnodes];
		// for back reference, build a mapping from APT states to local IDs
		id = new HashMap<State,Integer>();

		// tree-building starts at the initial state
		State active = ts.getInitialState();
		// we remember the number of the state we are working on ...
		int start = 0;
		// as well as the last state on our list so far
		int last = start;
		// for the initial state, obtain a new SNode with no father
		nodes[start] = new SNode(active,start,-1,-1);
		// exactly one (empty) path to initial state
		paths[start] = BigInteger.ONE;
		minpaths[start] = BigInteger.ONE;
		// last node of same depth
		int last_of_same_depth = last;
		// and save APT state and local ID in our list
		id.put(active,start);

		while (start <= last) {
			InterrupterRegistry.throwIfInterruptRequestedForCurrentThread();
			for (int num = start; num <= last_of_same_depth; num++) {
				active = nodes[num].s;
				Map<Integer,Integer> multilabel = new HashMap<Integer,Integer>();
				Map<Integer,State> modify = new HashMap<Integer,State>();
				for (Arc a : ts.getPostsetEdges(active)) {
					int lab_id = determineLabel(label2id.get(a.getLabel()),multilabel);
					if (label2id.get(a.getLabel()) != lab_id) {
						modify.put(lab_id, a.getTarget());
					}
					int target_id;
					if (!id.containsKey(a.getTarget())) {
						nodes[++last] = new SNode(a.getTarget(),last,num,lab_id);
						id.put(a.getTarget(),last);
						target_id = last;
					} else target_id = id.get(a.getTarget());
					if (shallowtree && target_id > last_of_same_depth) {
						if (paths[target_id] == null) {
							paths[target_id] = paths[num];
							minpaths[target_id] = paths[num];
						} else {
							if (minpaths[num].compareTo(minpaths[target_id]) == -1) {
								minpaths[target_id] = paths[num];
								nodes[target_id] = new SNode(nodes[target_id].s,target_id,num,lab_id);
							}
							paths[target_id] = paths[target_id].add(paths[num]);
						}
					}
				}
				for (Map.Entry<Integer,State> mi : modify.entrySet()) {
					int oldlab = mi.getKey();
					while (labelref.get(oldlab)>=0) oldlab = labelref.get(oldlab);
					ts.removeArc(ts.getArc(active, mi.getValue(), id2label.get(oldlab)));
					ts.createArc(active, mi.getValue(), id2label.get(mi.getKey()));
				}
			}
			for (int num = start; num <= last_of_same_depth; num++) {
				active = nodes[num].s;
				for (Arc a : ts.getPostsetEdges(active)) {
					nodes[num].createEdge(label2id.get(a.getLabel()),id.get(a.getTarget()));
				}
			}
			start = last_of_same_depth + 1;
			last_of_same_depth = last;
		}
/*
		// loop through all detected states (over variable num)
		do {
			InterrupterRegistry.throwIfInterruptRequestedForCurrentThread();
			// num is the main variable of this loop, so let's acquire the according state
			active = nodes[num].s;
			Map<Integer,Integer> multilabel = new HashMap<Integer,Integer>();
			Map<Integer,Integer> modify = new HashMap<Integer,Integer>();

			// now build the spanning tree by adding SNodes for the targets of all edges
			// from this state; we work on SNodes in the order they are added, this
			// ensures that we construct a breadth-first spanning tree
			for (Arc a : ts.getPostsetEdges(active)) {
				// to avoid non-determinism, provide a first relabelling if necessary
				int lab_id = determineLabel(label2id.get(a.getLabel()),multilabel);
				// if the target is already in our list, the edge does not belong
				// to the spanning tree, but is a "chord"
				if (id.containsKey(a.getTarget())) {
					// we then just add the edge to our local structure
					nodes[num].createEdge(lab_id,id.get(a.getTarget()));
				} else {
					// the new target state is acquired (with label and father)
					nodes[++last] = new SNode(a.getTarget(),last,num,lab_id);
					nodes[num].createEdge(lab_id,last);
					// we also add the target to our translation list
					id.put(a.getTarget(),last);
				}
				// mark the arc for modification if necessary
				if (label2id.get(a.getLabel()) != lab_id)
					modify.put(lab_id, id.get(a.getTarget()));
			}
			// complete the relabeling in the original TS (cannot be done inside the Arc-loop)
			for (Map.Entry<Integer,Integer> mi : modify.entrySet()) {
				int oldlab = mi.getKey();
				while (labelref.get(oldlab)>=0) oldlab = labelref.get(oldlab);
				nodes[num].modifyTS(oldlab, mi.getKey(), mi.getValue());
			}
			// now go to the next state in the list until the list ends
		} while (++num <= last);
*/
		// return the number of processed states so we can check whether the LTS
		// is totally reachable
		return ++last;
	}


	/**
	 * For any chord (s,t,s') we must compute the chord cycle
	 * initial state -> s -t-> s' <- initial state and get the
	 * Parikh vector of the above walk, which belongs to the
	 * cycle basis if non-zero
	 *
	 * @param chord The number of the chord in the global chord list
	 * @return The Parikh vector of the chord cycle
	 */
	private Map<Integer,Integer> getChordParikh(int chord) {
		// create a Parikh vector for the result
		HashMap<Integer,Integer> hm = new HashMap<Integer,Integer>(nodes[chsource.get(chord)].parikh);
		// the chord label is added once to the result
		Integer val = hm.get(chlabel.get(chord));
		hm.put(chlabel.get(chord), (val==null ? 1 : val+1));
		// the distance of the sink state is subtracted
		for (Map.Entry<Integer,Integer> me : nodes[chsink.get(chord)].parikh.entrySet()) {
			val = hm.get(me.getKey());
			hm.put(me.getKey(), (val==null ? 0 : val)-me.getValue());
		}
		// lastly, we reduce the size of the mapping by
		// removing all zero entries in the Parikh vector mapping
		return removeZeros(hm);
	}

	/**
	 * For any state s we must compute the Parikh vector of its
	 * spanning tree path
	 *
	 * @param state The state s
	 * @return The Parikh vector for the state
	 */
	private Map<Integer,Integer> getStateParikh(int state) {
		return nodes[state].parikh;
	}

	/**
	 * Remove zero entries in a Parikh vector
	 *
	 * @param map The original Parikh vector (will be modified)
	 * @return The modified Parikh vector
	 */
	private Map<Integer,Integer> removeZeros(Map<Integer,Integer> map) {
		Iterator<Map.Entry<Integer,Integer>> it = map.entrySet().iterator();
		while (it.hasNext())
			if (it.next().getValue() == 0) it.remove();
		return map;
	}

	/**
	 * Compute the cycle basis for the current transition system
	 */
	private void cycleBasis() {
		// clear the old basis, not usable anymore
		cyclebasis.clear();
		chordbasis.clear();
		Map<Map<Integer,Integer>,Integer> comp = new HashMap<Map<Integer,Integer>,Integer>();
		// look at all chords
//System.out.print("CYCBASE");
		for(int i=0; i<chsource.size(); i++) { 
			// but only those still usable for solutions
			if (chrenamed.get(i)) continue; // remove this if chord labels can be renamed to old labels
			// compute the (extended) Parikh vector of the chord
			Map<Integer,Integer> cp = getChordParikh(i);
			// only non-zero Parikh vectors can enter the cycle basis
			if (cp.size()==0) continue;
			// check if it is already there
			Integer pos = comp.get(cp);
			// if not, we add it to our data structures
			if (pos == null) {
				pos = cyclebasis.size();
				comp.put(cp,pos);
				cyclebasis.add(cp);
				HashSet<Integer> cbs = new HashSet<Integer>();
				cbs.add(i);
				chordbasis.add(cbs);
			// otherwise we just add the chord to the existing list
			} else	chordbasis.get(pos).add(i);
//System.out.print("(");
//for(Map.Entry<Integer,Integer> me : cp.entrySet()) System.out.print(id2label.get(me.getKey())+":"+me.getValue()+" ");
//System.out.print(")->"+pos+" ");
		}
//System.out.println();
	}

	/**
	 * Convert the position of a variable in the ESSP dual system to an index in cyclebasis
	 *
	 * @param varpos The position of the variable representing a cycle
	 * @param statevars The list of state variables produces with the inequality system
	 * @return The index in the cyclebasis at which the corresponding Parikh vector and chords are found
	 */
	private int getCycleIndex(int varpos, ArrayList<Integer> statevars) {
		return (varpos/2-statevars.size())/2;
	}

	/**
	 * Construct the dual inequality system for an SSP instance
	 *
	 * @param state1 The first state of the SSP
	 * @param state2 The second state of the SSP
	 * @param statevars The list of state variables (produced with the inequality system, use empty dummy)
	 * @return The inequality system
	 */
	private InequalitySystem buildSSPDualSystem(int state1, int state2, ArrayList<Integer> statevars) {
		return buildDualSystem(false,state1,state2,statevars);
	}

	/**
	 * Construct the dual inequality system for an ESSP instance
	 *
	 * @param state The state of the ESSP
	 * @param forbiddenlabel A label not enabled at the state (from the ESSP)
	 * @param statevars The list of state variables (produced with the inequality system, use empty dummy)
	 * @return The inequality system
	 */
	private InequalitySystem buildESSPDualSystem(int state, int forbiddenlabel, ArrayList<Integer> statevars) {
		return buildDualSystem(true,state,forbiddenlabel,statevars);
	}

	/**
	 * Build an inequality system for the dual (E)SSP problem at hand, using Farkas' Lemma
	 *
	 * @param system Whether to solve an ESSP (with obj as forbidden label) or an SSP (with obj as 2nd state)
	 * @param state The state s of an ESSP(s,t) or an SSP(s,s')
	 * @param obj The label t of an ESSP(s,t) or the state s' in SSP(s,s')
	 * @param statevars A reference from variables to states, initially empty
	 * @return The inequality system representing the dual of ESSP(s,t) or SSP(s,s')
	 */
	private InequalitySystem buildDualSystem(boolean system, int state, int obj, ArrayList<Integer> statevars) {
		// we get a column for each state that allows the label
		Set<Integer> states;
		if (system) states = enabled.get(obj);
		else { states = new HashSet<Integer>(); states.add(obj); }
		int numvars = states.size();
		// and two for each cycle of the cycle basis (depends on which one we use)
		if (truecyclebasis.isEmpty()) numvars += 2*cyclebasis.size();
		else numvars += 2*truecyclebasis.size();
		// the coefficient matrix has rows for region variables,
		// i.e. one row for the initial value and two for each label (F(a) and B(a))
		int[][] coeff = new int[2*alphabetsize+1][numvars];
		int i=0;
		statevars.clear();
		// state columns come first
		for (int st : states) {
			// for easy identification of states with variables
			statevars.add(st);
			// The state's Parikh vector is entered in the F(a) and B(a) columns
			// (negatively in B(a)) for each label a
			for (Map.Entry<Integer,Integer> me : getStateParikh(st).entrySet()) {
				coeff[2*me.getKey()+1][i] = me.getValue();
				coeff[2*me.getKey()+2][i] = -me.getValue();
			}
			// the forbidden label (allowed at this state) is subtracted
			if (system) coeff[2*obj+2][i]--;
			// and the initial region value is added
			coeff[0][i++] = 1;
		}
		// each cycle gets two columns, one of which is the negation of the other
		// as an effect we have an equality (instead of two inequalities) in the region
		// system, but the dual system is a different matter
		if (truecyclebasis.isEmpty()) { // if we do not use the true cycle basis, take all cycles
			for (int cyc = 0; cyc<cyclebasis.size(); cyc++) {
				for (Map.Entry<Integer,Integer> me : cyclebasis.get(cyc).entrySet()) {
					coeff[2*me.getKey()+1][i+2*cyc] = me.getValue();
					coeff[2*me.getKey()+2][i+2*cyc] = -me.getValue();
					coeff[2*me.getKey()+1][i+2*cyc+1] = -me.getValue();
					coeff[2*me.getKey()+2][i+2*cyc+1] = me.getValue();
				}
			}
		} else {
			for (int cyc = 0; cyc<truecyclebasis.size(); cyc++) {
				for (Map.Entry<Integer,Integer> me : cyclebasis.get(truecyclebasis.get(cyc)).entrySet()) {
					coeff[2*me.getKey()+1][i+2*cyc] = me.getValue();
					coeff[2*me.getKey()+2][i+2*cyc] = -me.getValue();
					coeff[2*me.getKey()+1][i+2*cyc+1] = -me.getValue();
					coeff[2*me.getKey()+2][i+2*cyc+1] = me.getValue();
				}
			}
		}

		// for the inequation system Ax<=b, the above builds the matrix A
		// now we need to construct b, which is built from the Parikh vector
		// of the state where the label is forbidden
		int[] b = new int[2*alphabetsize+1];
		for (Map.Entry<Integer,Integer> me : getStateParikh(state).entrySet()) {
			b[2*me.getKey()+1] = me.getValue();
			b[2*me.getKey()+2] = -me.getValue();
		}
		// special case for ESSP(s,a) (subtract B(a) once):
		if (system) b[2*obj+2]--;
		b[0] = 1;

		// finally, we build the inequality system
		InequalitySystem is = new InequalitySystem();
		// and add each row
		for (int eq = 0; eq < 2*alphabetsize+1; eq++)
			is.addInequality(b[eq],">=",coeff[eq],"equation "+eq);
		// additionally, we must make all variables non-negative
		int[] row = new int[numvars];
		for (int nn = 0; nn < numvars; nn++) {
			row[nn] = 1;
			is.addInequality(0,"<=",row,"var "+nn+" nonnegative");
			row[nn] = 0;
		}
		if (!system) { row[0]=1; is.addInequality(1,"=",row,"state diff"); }
		return is;
	}


	/**
	 * If a dual inequality system has a solution, we must find a variable
	 * that belongs to a state and has a positive value. As a heuristic,
	 * we choose the variable with lowest depth in the TS.
	 * By eliminating such a variable
	 * we hope that the system becomes unsolvable as fast as possible
	 *
	 * @param solution A solution of the inequality system
	 * @param statevars Reference from variables to states
	 * @return The ID of the state with the best contribution to the solution 
	 */
	private int findMaxStateVar(List<BigInteger> solution, ArrayList<Integer> statevars) {
		// solutions have rational values for the variables
		// the lowest possible value is 0 = 0/1
		BigInteger num = BigInteger.ZERO;
		BigInteger denom = BigInteger.ONE;
		// state is the state with the highest contribution so far,
		// index counts through the variables of the solution
		int state = -1, index = 0, depth = -1;
		Iterator<BigInteger> it = solution.iterator(); 
		while (it.hasNext() && index < statevars.size()) {
			int st = statevars.get(index);
			// get the next rational value
			BigInteger num2 = it.next();
			BigInteger denom2 = it.next();
			// and compare it with the previous maximum
			if (((depth<0 || depth>nodes[st].depth) && !num2.equals(BigInteger.ZERO)) ||
				(depth==nodes[st].depth && num2.multiply(denom).compareTo(num.multiply(denom2))==1)) {
				num = num2;
				denom = denom2;
				state = st;
				depth = nodes[st].depth;
			}
			index++;
		}
		// note: denom is 1 exactly if it still in its initial state, so the following works
		if (denom == BigInteger.ONE) return -state-1;
		return state;
	}

	/**
	 * If a dual inequality system has a solution, we must find a cycle
	 * that contributes to the solution. As a heuristic, we choose the cycle
	 * with the least number of different chord labels for its chords.
	 * By eliminating such a variable
	 * we hope that the system becomes unsolvable as fast as possible
	 *
	 * @param solution A solution of the inequality system
	 * @param statevars Reference from variables to states
	 * @return The ID of the best cycle 
	 */
	private int findBestCycle(List<BigInteger> solution, ArrayList<Integer> statevars) {
		// go through the solution variables
		Iterator<BigInteger> it = solution.iterator();
		int varnum = -1, found = -1, chnum = 0;
		while (it.hasNext()) {
			BigInteger val = it.next();
			// skip the state variables
			if (++varnum < 2*statevars.size()) continue;
			// skip unused cycles, check numerators only
			if (varnum % 2 == 1 || val.equals(BigInteger.ZERO)) continue;
			int pos = getCycleIndex(varnum, statevars);
			if (!truecyclebasis.isEmpty()) pos = truecyclebasis.get(pos);
			// count the chord labels for this cycle
			Set<Integer> labels = new HashSet<Integer>();
			for (int chord : chordbasis.get(pos))
				labels.add(chlabel.get(chord));
			// and look for the least value
			if (labels.size() < chnum || chnum == 0) {
				found = pos; 
				chnum = labels.size();
			}
		}
		return found;
	}

	/**
	 * Modify the label of an edge that is on the spanning tree path of exactly one of two given states.
	 *
	 * @param state1 One of the two states.
	 * @param state2 The other state (must be different!)
	 * @param preferred The preferred label to rename, or -1 if none
	 * @param newlabel The label to rename to if a preferred label is given (or -1), otherwise ignored 
	 */
	private int modifySpan(int state1, int state2, int preferred, int newlabel) {
		// first a dummy set for the calls to branchingPoint()
		Set<Integer> empty = new HashSet<Integer>();
		// get the first node on state1's own spanning tree branch (or -1 if fully covered by state2)
		int branch = branchingPoint(state1,state2,empty);
		// if we have a preferred label that should be renamed, look for it
		if (preferred>=0) {
			// first from state1 backwards until the spanning tree branches of state1/state2 meet
			int st = state1;
			// check if state1 has its own branch at all
			if (branch>=0) while (true) {
				// if we find our label, change it and stop
				if (nodes[st].span_label == preferred) {
					if (newlabel<0) newlabel = createLabel(preferred);
					nodes[nodes[st].father].relabelEdge(preferred,newlabel);
					return st;
				}
				// exit in the middle of the loop; we need one extra check at the end
				if (st == branch) break;
				// move towards the root upto the branching point
				st = nodes[st].father;
			}
			// if we did not find the preferred label on this path, check the one for state2
			int branch2 = branchingPoint(state2,state1,empty);
			st = state2;
			if (branch2>=0) while (true) {
				if (nodes[st].span_label == preferred) {
					if (newlabel<0) newlabel = createLabel(preferred);
					nodes[nodes[st].father].relabelEdge(preferred,newlabel);
					return st;
				}
				if (st == branch2) break;
				st = nodes[st].father;
			}
			// if this did not succeed either, just choose 'any' edge
		}
		// in case state1 is on the spanning tree path of state2, use the branch of state2
		if (branch<0) branch = branchingPoint(state2,state1,empty);
		// get a new label
		int label = createLabel(nodes[branch].span_label);
		// and relabel the first possible edge (nearest to root) to hopefully solve also other SSPs
		nodes[nodes[branch].father].relabelEdge(nodes[branch].span_label, label);
		return branch;
	}

	/**
	 * Modify one edge of each cycle with a given Parikh vector so that the current solution
	 * of a dual (E)SSP system is prevented. The Parikh vector of the cycles must occur in
	 * the solution and will not exist anymore afterwards. 
	 *
	 * @param chpos The position of the Parikh vector of the cycles in the cyclebase.
	 * @param state1 One of two states that occur in the solution.
	 * @param state2 The other state (must be different)
	 */
	private void modifyCycle(int chpos, int state1, int state2) {
		// define a map oldlabel->newlabel to prevent multiple new labels for the same old one
		Map<Integer,Integer> labelmap = new HashMap<Integer,Integer>();
		// run through all the chords for the given element of the cyclebasis
		for (int ch : chordbasis.get(chpos)) {
			// the label of the chord is the only one where renaming is guaranteed to work
			int rename_label = chlabel.get(ch);
			// check if we already renamed this label for another chord
			Integer new_label = labelmap.get(rename_label);
			if (new_label == null) {
				// if not, get a new label
				new_label = createLabel(rename_label);
				labelmap.put(rename_label, new_label);
			}
			// finally, rename the label of this chord
			nodes[chsource.get(ch)].relabelEdge(rename_label, new_label);
			chrenamed.set(ch, true);
		}
	}

	/**
	 * Check all SSP based on equal Parikh vectors and fix them by relabeling
	 */
	private void checkSimpleSSP() {
		// we first need a semi-equivalence, states in different classes are non-equivalent
		// all possible-equivalent states in a class have the same depth in TS
		// the classes are sorted by increasing depth
		listParikhEquivalence(); // creates global peqlist
		// now we go through the equivalence classes
		for (int index=0; index<peqlist.size(); index++) {
			// take two swappable sets, one containing the states to process now,
			Set<Integer> peqset = peqlist.get(index);
			// the other one for saving their fathers for the next run (breadth-first)
			Set<Integer> newset = new HashSet<Integer>();
			// the states we start with are marked as being contained in SSP
			for (int st : peqset) nodes[st].sspstate = true;
			// now we process the states
			while (!peqset.isEmpty()) {
				// one by one
				int st = peqset.iterator().next();
				peqset.remove(st);
				SNode state = nodes[st];
				int father = state.father;
				// if the state has a father, we process the father later
				if (father >= 0) newset.add(father);
				// is this is the last state in the current package, swap the sets
				// in the next run of the loop, we will then start working on the fathers
				if (peqset.isEmpty()) { 
					Set<Integer> tmpset = peqset;
					peqset = newset; 
					newset = tmpset; 
				}

				// if the state has no father, nothing needs to be done
				if (father < 0) continue;

				SNode fa = nodes[father];
				int lab = state.span_label;
				// firstpath is some path leading backwards, from a successor, to this state
				if (state.firstpath == null)
					state.firstpath = new ArrayList<Integer>();
				// if this state is a splitter (states of the same equivalence class are
				// reachable via different edges from this state) or we got an explicit
				// kill signal (when different equivalence classes meet here via different
				// edges), the firstpath becomes obsolete
				if (!state.renamingpaths.isEmpty() || state.kill)
					state.firstpath.clear();
				// when we go backwards across an edge, it is added to the firstpath
				state.firstpath.add(lab);
				// so the firstpath is the path from the last point where two processed
				// states had the same father

				// if we encounter a different path made by our own equivalence class
				if (fa.classlabels.containsKey(index)) {
					// we check if the other path was a 'first', in which case
					// we must enter that firstpath (stored with the father) and
					// our own one into the renamingpaths
					if (fa.firstpath != null) {
						if (fa.renamingpaths.isEmpty())
							fa.lastkill = true; // signal the next splitter
							// on our way that the firstpath we will be bringing
							// is something new and must be handled
						copyCut(fa.renamingpaths, fa.firstpath);
						fa.firstpath = null;
					}
					// otherwise there was a meeting in our equivalence class here
					// earlier in time, and we only save our own firstpath
					copyCut(fa.renamingpaths, state.firstpath);
					// the classlabels mapping equivalence classes to the spanning
					// tree edges of this state, are modified accordingly
					if (fa.classlabels.get(index).add(lab)) {
						// for incremental/decremental operations we also use a counter
						Integer lc = fa.labelcounter.get(lab);
						fa.labelcounter.put(lab, (lc==null ? 1 : lc+1));
					}
				} else {
					// we did not meet another path from our own equivalence class
					// we just reserve some space in the classlabels
					Set<Integer> tmp = new HashSet<Integer>();
					tmp.add(lab);
					fa.classlabels.put(index, tmp);
					// and pass on the firstpath to our father
					fa.firstpath = state.firstpath;
					// but if father is a splitter, we might need to update his renaimgpaths
					if (fa.lastkill && !fa.renamingpaths.isEmpty()) {
						fa.lastkill = false;
						if (fa.renamingpaths.containsKey(lab))
							copyCut(fa.renamingpaths, fa.firstpath);
					} else {
						// if father is not a splitter, but different equivalence classes
						// meet there, we must signal that to the next splitter we see
						int diff = fa.classlabels.size()-state.classlabels.size();
						if (state.sspstate) diff--;
						if (diff > 0) {
							// notify father to start a new firstpath
							// [why is this flag necessary? why not just delete firstpath?]
							fa.kill = true;
							fa.lastkill = true;
						}
					}
					// update the counter for classlabels
					Integer lc = fa.labelcounter.get(lab);
					fa.labelcounter.put(lab, (lc==null ? 1 : lc+1));
				}
				// remove invalid data (reinit for later)
				state.lastkill = false;
				state.firstpath = null;
			}
		}

		// we have done some preprocessing now
		// renamingpaths contains (for each label) a path on which a renaming can occur
		// classlabels contains (for each class) a set of renamingpaths; all but one of which must endure a renaming
		// when we remove a label from some set in classlabels, we can use labelcounter to
		// check if this was the last label of its kind at this state. If so, the corresponding
		// renamingpath becomes obsolete.

		// now we do the real work (no fun!)
		solveSimpleSSP();
	}

	/**
	 * Copy or cut a renaming path according to a given firstpath
	 *
	 * @param The renaming paths, one of which must be modified. Either a new path will be added
	 *	  or an existing one will be cut down to a common prefix
	 * @param newpath The path to match against the renaming paths
	 */
	public void copyCut(Map<Integer,ArrayList<Integer>> choice, ArrayList<Integer> newpath) {
		// do nothing if the new path is empty
		if (newpath.size()<1) return;
		// find the label under which the appropriate renaming path is stored in 'choice'
		int lab = newpath.get(newpath.size()-1);
		// get it
		ArrayList<Integer> cmp = choice.get(lab);
		// if it is not there, we copy 'newpath' to it, in reverse order (since firstpath
		// builds paths from back to front)
		if (cmp == null) {
			choice.put(lab, newpath);
			int tmp;
			for (int i=0,j=newpath.size()-1; i<j; i++,j--) {
				tmp = newpath.get(i);
				newpath.set(i,newpath.get(j));
				newpath.set(j,tmp);
			}
			return;
		}
		// if we find it, we find the first difference with newpath and cut off everything from there
		int index = 0;
		for (int i=newpath.size(); --i>=0; index++) {
			if (index >= cmp.size()) return;
			if (newpath.get(i)!=cmp.get(index)) break;
		}
		for (int i=cmp.size()-1; i>=index; i--) cmp.remove(i);
	}

	/**
	 * Construct the equivalence classes of states with equivalent Parikh vectors for simple SSP.
	 * The classes will be held in the global variable peqlist. This list must not be modified.
	 * For each state, its peqindex will point to the set in peqlist containing it, unless the
	 * state forms its own class, then the peqindex will be -1.
	 */
	private void listParikhEquivalence() {
		// we build a temporary map first, adding elements is easier here
		// parameters are 1) depth 2) Parikh vector 3) Set of states with properties 1)+2)
		Map<Integer,Map<Map<Integer,Integer>,Set<Integer>>> tmppeqlist = new HashMap<Integer,Map<Map<Integer,Integer>,Set<Integer>>>();
		int maxdepth = -1;
		// for all states ...
		for (int st=0; st<numnodes; st++) {
			// get the depth-map according to this states' depth
			Map<Map<Integer,Integer>,Set<Integer>> dlist = tmppeqlist.get(nodes[st].depth);
			if (dlist == null) {
				dlist = new HashMap<Map<Integer,Integer>,Set<Integer>>();
				tmppeqlist.put(nodes[st].depth,dlist);
			}
			// get the set of states (so far) with the same Parikh vector
			Set<Integer> eqset = dlist.get(nodes[st].parikh);
			if (eqset == null) {
				eqset = new HashSet<Integer>();
				dlist.put(nodes[st].parikh,eqset);
			}
			// add our state
			eqset.add(st);
			// adapt the maximal depth for easier iteration later
			if (maxdepth < nodes[st].depth) maxdepth = nodes[st].depth;
		}
		// now build the real thing, the equivalence (held globally)
		peqlist = new ArrayList<Set<Integer>>();
		int index = 0;
		// we build it by increasing depth
		for (int d=0; d<=maxdepth; d++) {
			Map<Map<Integer,Integer>,Set<Integer>> dlist = tmppeqlist.get(d);
			if (dlist == null) continue;
			// for each occurring depth visit the sets of states 
			for (Set<Integer> sit : dlist.values()) {
				// only sets which at least two states can form SSP
				if (sit.size()<2) continue;
				// notify the state which class it is in
				for (int st : sit) nodes[st].peqindex = index;
				// and add the class to the equivalence
				peqlist.add(sit);
				index++;
			}		
		}
	}

	/**
	 * Solve an SSP for two states with equivalent Parikh vectors
	 */
	private void solveSimpleSSP() {
		// part 1: we collect an array of sets of splitter states, states in the same set
		// have the same splitter depth = index (i.e. number of other splitter states on the
		// spanning tree path of the splitter)
		ArrayList<Map<Integer,Integer>> classes = new ArrayList<Map<Integer,Integer>>();
		Map<Integer,Integer> map1,map2;
		map1 = new HashMap<Integer,Integer>();
		// nextDepth collects the next splitter successors of all states in the set
		// initially, this means all splitters directly reachable from the initial state
		// without passing other splitters
		map2 = nextDepth(map1);
		do {
			map1 = map2;
			map2 = nextDepth(map1);
			classes.add(map1);
		} while (!map2.isEmpty());

		// part 2: now we go through the splitter classes, starting with the highest depth.
		// all splitter states require a renaming of some label; we start at the back end
		for(int index=classes.size(); --index>=0; ) {
			// we need to build some new data structures
			// 'laboccur' will contain for each label a set of splitters (of the current
			// class) where a renaming of this label is possible
			Map<Integer,Set<Integer>> laboccur = new HashMap<Integer,Set<Integer>>();
			// now we visit the splitters of our class
			for (Map.Entry<Integer,Integer> me : classes.get(index).entrySet()) {
				int st = me.getKey();

				// 'subtreelabels' will contain the new labels (created by this
				// method) that occur in the whole subtree starting at a direct
				// successor state of this splitter; this state is identified
				// by its spanning tree label (leading back to the splitter).
				nodes[st].subtreelabels = new HashMap<Integer,Set<Integer>>();
				// go through all direct-successor-splitters (of the next higher depth)
				for (int st2 : nodes[st].nextbranch) {
					// get the span label at our splitter that leads to the successor
					int mylabel = classes.get(index+1).get(st2);
					Set<Integer> labels = nodes[st].subtreelabels.get(mylabel);
					if (labels == null) {
						labels = new HashSet<Integer>();
						nodes[st].subtreelabels.put(mylabel, labels);
					}
					// just collect the new labels of the successor-splitter and
					// add them to our set
					labels.addAll(nodes[st2].inheritablelabels);
				}

				// for reusing labels it is necessary to find out which labels we can
				// safely use. 'inheritables' are all new labels occurring at sucessors,
				// while 'multilabels' are those that occur after at least two different
				// spanning tree labels after our splitter. Such labels cannot be reused
				// at our splitter, but we may pass them on to the next splitter of lower
				// depth
				nodes[st].inheritablelabels = new HashSet<Integer>();
				Set<Integer> multilabels = new HashSet<Integer>();
				// relabellings will be delayed, so we need to store the state,
				// the old label, and the new label for a later call of relabelEdge() 
				ArrayList<Integer> rstate = new ArrayList<Integer>();
				ArrayList<Integer> roldlabel = new ArrayList<Integer>();
				ArrayList<Integer> rnewlabel = new ArrayList<Integer>();
				// now take a look at all span labels going forward from our splitter
				for (int lab : nodes[st].span) {
					// we obtain the inherited subtreelabels for such a label (if any)
					Set<Integer> lset = nodes[st].subtreelabels.get(lab);
					if (lset == null) { 
						nodes[st].subtreelabels.put(lab,new HashSet<Integer>()); 
						continue;
					}
					// if some label in the set cannot be added to our inheritable labels
					// (because it is already there), it is a multilabel and
					// excluded from renamings at this splitter
					for (int lab2 : lset) {
						if (!nodes[st].inheritablelabels.add(lab2))
							multilabels.add(lab2);
					}
				}
				// before we find out which labels we can reuse, we must consolidate our
				// data structures. This will remove equivalence class entries in classlabels
				// if there is at most one path onwards for the class, and it will also
				// remove renamingpaths that are not pointed to anymore via classlabels 
				consolidateRenamingPaths(st, null, null);

				// this is the main loop for inheriting labels
				for (int lab : nodes[st].span) {
					// if there is no renamingpath for this label, we are done
					ArrayList<Integer> path = nodes[st].renamingpaths.get(lab);
					if (path == null) continue;
					// 'newlabels' will point old labels to sets of available new labels
					Map<Integer,Set<Integer>> newlabels = new HashMap<Integer,Set<Integer>>();
					// we compare now the new labels in the subtree with the renamingpath
					for (int lab2 : nodes[st].subtreelabels.get(lab)) {
						// but only allowed labels are considered
						if (!multilabels.contains(lab2)) {
							// these we collect ...
							Set<Integer> newset = newlabels.get(relabelling.get(lab2));
							if (newset == null) {
								newset = new HashSet<Integer>();
								newlabels.put(relabelling.get(lab2), newset);
							}
							newset.add(lab2);
						}
					}
					// time for the comparison, so we walk the renamingpath
					for (int i=0; i<path.size(); i++) {
						// and check if a label there could be replaced by reusing
						Set<Integer> val = newlabels.get(path.get(i));
						// if so ...
						if (val != null) {
							int lab2 = val.iterator().next();
							// relabel path.get(i) to lab2(=reusable)
							// find the state where this edge occurs
							int st2 = st;
							for (int j=0; j<i; j++) st2 = nodes[st2].edges.get(path.get(j));
							// notify ourselves to later relabel
							rstate.add(st2);
							roldlabel.add(path.get(i));
							rnewlabel.add(lab2);
							// delete this renamingpath and consolidate our data
							deleteRenamingPath(st, lab, null, null);
							consolidateRenamingPaths(st, null, null);
							break;
						}
					}
				}
				// relabel the marked edges now
				for (int i=0; i<rstate.size(); i++)
					nodes[rstate.get(i)].relabelEdge(roldlabel.get(i),rnewlabel.get(i));

				// so far we have only inherited labels, but not created new ones
				// to do this efficiently, we need some counters
				// laboccur will point each label to the set of states where this label can be renamed
				// rpcount will count for each label in which renamingpaths it occurs
				Map<Integer,Set<Integer>> count = new HashMap<Integer,Set<Integer>>();
				for (int lab : nodes[st].span) {
					// go thorugh all existing renamingpaths
					ArrayList<Integer> path = nodes[st].renamingpaths.get(lab);
					if (path != null) for (int i=0; i<path.size(); i++) {
						// get path label
						int lab2 = path.get(i);
						// select the according set in count
						Set<Integer> val = count.get(lab2);
						if (val == null) { 
							val = new HashSet<Integer>(); 
							count.put(lab2,val); 
						}
						// and add the span label to it
						val.add(lab);
						// add our splitter to laboccur
						val = laboccur.get(lab2);
						if (val == null) {
							val = new HashSet<Integer>(); 
							laboccur.put(lab2,val);
						}
						val.add(st);
					}
				}
				// save 'count' at our splitter
				nodes[st].rpcount = count;
			}

			// for laboccur we also need a counter that can order
			// the entries by number of occurrences with low complexity
			// 'laborder' gives for each number i the labels that can be
			// renamed at exactly i different states
			TreeMap<Integer,Set<Integer>> laborder = new TreeMap<Integer,Set<Integer>>();
			for(Map.Entry<Integer,Set<Integer>> me : laboccur.entrySet()) {
				Set<Integer> val = laborder.get(me.getValue().size());
				if (val == null) {
					val = new HashSet<Integer>();
					laborder.put(me.getValue().size(), val);
				}
				val.add(me.getKey());
			}

			// now we come to the main loop that creates new labels
			// as long as laborder is not empty, there is a relabelling to be done
			while (!laborder.isEmpty()) {
				// get the highest key in laborder, i.e. a label that can be
				// renamed most often
				Set<Integer> highest = laborder.lastEntry().getValue();
				// just one of those labels is enough for now
				int lab = highest.iterator().next();
				// get the states at which we can rename this label
				// note: we copy this set here, as laboccur can be modified along the way
				Set<Integer> states = new HashSet<Integer>(laboccur.get(lab));
				// if there is more than one instance to relabel we are nailed to this label
				if (states.size()>1) {
					// create a replacement label
					int newlabel = createLabel(lab);
					relabelling.put(newlabel, lab);
					// visit all the states at which the relabelling can occur	
					for (int st : states) {
						// we can bequeath this new label later 
						nodes[st].inheritablelabels.add(newlabel);
						// of all the renamingpaths where the label occurs
						Set<Integer> spanchoices = nodes[st].rpcount.get(lab);
						// we try to find a shortest one (eliminating as few choices as possible)
						int min = -1, edge = -1;
						for (int spanedge : spanchoices)
							if (min==-1 || min>nodes[st].renamingpaths.get(spanedge).size()) {
								min = nodes[st].renamingpaths.get(spanedge).size();
								edge = spanedge;
							}
						// then we look for the label on this renamingpath
						int st2 = st;
						for (int lab2 : nodes[st].renamingpaths.get(edge)) {
							if (lab2 == lab) {
								// and when we find it, we relabel the edge
								nodes[st2].relabelEdge(lab,newlabel);
								break;
							}
							st2 = nodes[st2].edges.get(lab2);
						}
						// finally, we consolidate our data structures again
						deleteRenamingPath(st, edge, laborder, laboccur);
						consolidateRenamingPaths(st, laborder, laboccur);
					}
				} else {
					// in case there is only one state at which a relabelling must occur
					int st = states.iterator().next();
					// we go through all renamingpaths containing the label
					Set<Integer> spanchoices = nodes[st].rpcount.get(lab);
					int max = -1, edge = -1, label = -1;
					for (int spanedge : spanchoices) {
						for (int lab2 : nodes[st].renamingpaths.get(spanedge)) {
							// we may select any label, but it should occur
							// as often as possible on the spanning tree
							// path of this state, so that it can be inherited
							// and reused as often as possible
							Integer val = nodes[st].parikh.get(lab2);
							if (val == null) val=0;
							if (max < val) {
								max = val;
								label = lab2;
								edge = spanedge;
							}
						}
					}
					// now we create a replacement for the newly selected label
					int newlabel = createLabel(label);
					relabelling.put(newlabel, label);	
					// bequeath it
					nodes[st].inheritablelabels.add(newlabel);
					// and look for it on the renaming path
					int st2 = st;
					for (int lab2 : nodes[st].renamingpaths.get(edge)) {
						if (lab2 == label) {
							// to finally relabel it
							nodes[st2].relabelEdge(label,newlabel);
							break;
						}
						st2 = nodes[st2].edges.get(lab2);
					}
					// as always, the data structures are consolidated
					deleteRenamingPath(st, edge, laborder, laboccur);
					consolidateRenamingPaths(st, laborder, laboccur);
				}
			}
		}
	}

	/**
	 * Consolidate the classlabels and renamingpaths of some state
	 *
	 * @param st The state.
	 * @param laborder Map from number of states to sets of labels (partly inverse of laboccur);
	 *	  null is also allowed in which case the laborder/laboccur data is not updated
	 * @param laboccur Map from labels to set of states where the label can be renamed;
	 *	  null is also allowed in which case the laborder/laboccur data is not updated
	 */
	private void consolidateRenamingPaths(int st, TreeMap<Integer,Set<Integer>> laborder, Map<Integer,Set<Integer>> laboccur) {
		// first eliminate all entries in classlabels where the value-part contains less than 2 elements
		// labcounter is also updates
		Iterator<Map.Entry<Integer,Set<Integer>>> it = nodes[st].classlabels.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry<Integer,Set<Integer>> me = it.next();
			if (me.getValue().size()==1) { 
				int lab = me.getValue().iterator().next();
				me.getValue().remove(lab);
				nodes[st].labelcounter.put(lab,nodes[st].labelcounter.get(lab)-1);
			}
			if (me.getValue().isEmpty()) it.remove();
		}
		// then check which renamingpaths have become obsolete (as labcounter has a zero entry for them)
		Iterator<Map.Entry<Integer,Integer>> it2 = nodes[st].labelcounter.entrySet().iterator();
		while (it2.hasNext()) {
			Map.Entry<Integer,Integer> me = it2.next();
			if (me.getValue()==0) {
				deleteRenamingPath(st, me.getKey(), laborder, laboccur);
				it2.remove();
			}
		}
	}

	/**
	 * Delete a given renamingpath, also updating other data structures 
	 *
	 * @param st The state at which the renamingpath should be deleted.
	 * @param edge The edge at this state pointing to the renamingpath.
	 * @param laborder Map from number of states to sets of labels (partly inverse of laboccur);
	 *	  null is also allowed in which case the laborder/laboccur data is not updated
	 * @param laboccur Map from labels to set of states where the label can be renamed;
	 *	  null is also allowed in which case the laborder/laboccur data is not updated
	 */
	private void deleteRenamingPath(int st, int edge, TreeMap<Integer,Set<Integer>> laborder, Map<Integer,Set<Integer>> laboccur) {
		// first adapt laborder/laboccur if given, this also includes rpcount
		if (laborder != null) for (int lab2 : nodes[st].renamingpaths.get(edge)) {
			Set<Integer> rpc = nodes[st].rpcount.get(lab2);
			if (rpc == null) continue;
			rpc.remove(edge);
			if (rpc.isEmpty()) {
				nodes[st].rpcount.remove(lab2);
				Set<Integer> val = laboccur.get(lab2);
				laborder.get(val.size()).remove(lab2);
				if (laborder.get(val.size()).isEmpty())
					laborder.remove(val.size());
				val.remove(st);
				if (val.isEmpty())
					laboccur.remove(lab2);
				else {
					if (!laborder.containsKey(val.size()))
						laborder.put(val.size(), new HashSet<Integer>());
					laborder.get(val.size()).add(lab2);
				}
			}
		}
		// then remove the renamingpath and reduce classlabels/labcounter
		nodes[st].renamingpaths.remove(edge);						
		for (Map.Entry<Integer,Set<Integer>> me : nodes[st].classlabels.entrySet())
			if (me.getValue().remove(edge)) {
				int val = nodes[st].labelcounter.get(edge)-1;
				if (val>0) nodes[st].labelcounter.put(edge,val);
				else nodes[st].labelcounter.remove(edge);
			}
	}

	/**
	 * Given any set of states, find all direct-successor splitter states.
	 *
	 * @param states A map from the states to any Integer (will be ignored). Can be empty on first call.
	 * @return A map from the next splitter states to the edge(label) which must be used
	 *	   at the original state to reach the successor splitter
	 */
	private Map<Integer,Integer> nextDepth(Map<Integer,Integer> states) {
		// if called with empty map
		if (states.isEmpty()) {
			// we put the initial state into the map
			states.put(0,-1);
			// if it is a splitter state, we return it
			if (!nodes[0].renamingpaths.isEmpty()) return states;
			// otherwise it is used as the starting point
		}
		// tmp contains non-splitter states which are passed
		Map<Integer,Integer> tmp = new HashMap<Integer,Integer>();
		// result contains splitter states at which the search ends
		Map<Integer,Integer> result = new HashMap<Integer,Integer>();
		// for each initially given state
		for (int st : states.keySet()) {
			// collect all direct successors
			for (int lab : nodes[st].span)
				tmp.put(nodes[st].edges.get(lab), (nodes[st].renamingpaths.isEmpty() ? -1 : lab));
			// and process them until none is left
			while (!tmp.isEmpty()) {
				int st2 = tmp.entrySet().iterator().next().getKey();
				int reflab = tmp.get(st2);
				tmp.remove(st2);
				// if a state is not a splitter, put all dieect successors in tmp
				if (nodes[st2].renamingpaths.isEmpty())
					for (int lab : nodes[st2].span)
						tmp.put(nodes[st2].edges.get(lab), reflab);
				else {
					// otherwise put the state into the result set and mark it
					// as a direct-successor splitter of 'st'
					nodes[st].nextbranch.add(st2);
					result.put(st2, reflab);
				}
			}
		}
		return result;
	}


	/**
	 * The transition system with renamed labels
	 *
	 * @return The new transition system
	 */
	public TransitionSystem getTS() {
		return ts;
	}

	/**
	 * If the operation was successful (the lts is totally reachable)
	 *
	 * @return result
	 */
	public boolean getResult() {
		return result;
	}

}
