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

public class UnsolvableGenerator {

	public static void main(String[] args) {
		if (args.length != 2) {
			System.err.println("Arguments: (1) Class of unsolvable LTS, (2) Size of the LTS");
			return;
		}
		int size = -1;
		try {
			size = Integer.parseInt(args[1]);
		} catch (NumberFormatException e) {
			System.err.println("Second argument must be an integer");
			return;
		}
		if (size<1) size=1;
		System.out.println(".name \""+args[0]+" "+args[1]+"\"");
		System.out.println(".type LTS\n\n.states");
		switch (args[0]) {
			case "lincomb": linearComb(size); break;
			case "quadcomb": quadraticComb(size); break;
			case "staticcomb": staticComb(size); break;
			case "overlappingcycles": overlappingCycles(size); break;
			case "tree": abbaTree(size); break;
			case "twig": twig(size); break;
			case "lrtree": abcdTree(size); break;
			case "cycpath": cyclicPath(size,false); break;
			case "cycpath2": cyclicPath(size,true); break;
			case "knobcomb": knobComb(size); break;
			case "2cycles": generateCycle(2,size); break;
			case "size3cycles": generateCycle(size,3); break;
			case "grid": grid(size); break;
			case "2waycomb": twoWayComb(size); break;
			case "twig2": twig2(size); break;
			case "alter": alternate(size); break;
			case "gridb": gridB(size); break;
			case "gridb2": gridB2(size); break;
			case "abring": abring(size); break;
			case "abword": abword(size); break;
			case "2dimcyc": cyccopy(size); break;
		}
	}

	public static void cyccopy(int size) {
		for (int x=0; x<size; x++)
			for (int y=0; y<size; y++)
				if (x==0 && y==0) createInitialState("x0y0",0,0);
				else createState("x"+x+"y"+y,75*x,75*y);
		advanceToLabels();
		for (int x=0; x<size; x++) createLabel("a"+x);
		for (int y=0; y<size; y++) createLabel("b"+y);
		advanceToArcs();
		for (int x=0; x<size; x++)
			for (int y=0; y<size; y++) {
				createArc("x"+x+"y"+y,"a"+x,"x"+(x==size-1?0:x+1)+"y"+y);
				createArc("x"+x+"y"+y,"b"+y,"x"+x+"y"+(y==size-1?0:y+1));
		}
	}

	public static void abring(int size) {
		createInitialState("s0",0,0);
		for(int x=1; x<2*size; x++) createState("s"+x,75*x,0);
		createState("s"+(2*size),75*size,100);
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");
		advanceToArcs();
		for(int x=0; x<2*size; x++) 
			createArc("s"+x,(x%2==0?"a":"b"),"s"+(x+1));
		createArc("s"+(2*size),"c","s0");
	}

	public static void abword(int size) {
		createInitialState("s0",0,0);
		for(int x=1; x<2*size; x++) createState("s"+x,75*x,0);
		createState("s"+(2*size),75*size,100);
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for(int x=0; x<2*size; x++) 
			createArc("s"+x,(x%2==0?"a":"b"),"s"+(x+1));
	}

	public static void gridB(int size) {
		for (int x=0; x<=size; x++)
			for (int y=0; y<=size; y++) {
				if (x==0 && y==0) createInitialState("x0y0",0,0);
				else createState("x"+x+"y"+y,75*x,75*y);
			}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");
		advanceToArcs();
		for(int x=0; x<size; x++) createArc("x"+x+"y0","b","x"+(x+1)+"y0");
		for(int y=0; y<size; y++) createArc("x0y"+y,"a","x0y"+(y+1));
		for(int x=0; x<size; x++)
			for(int y=0; y<size; y++) {
				createArc("x"+x+"y"+(y+1),"b","x"+(x+1)+"y"+(y+1));
				createArc("x"+(x+1)+"y"+y,"a","x"+(x+1)+"y"+(y+1));
		}
		createArc("x"+size+"y"+size,"c","x0y0");
	}

	public static void gridB2(int size) {
		for (int x=0; x<=size; x++)
			for (int y=0; y<=size; y++) {
				if (x==0 && y==0) createInitialState("x0y0a",0,0);
				else createState("x"+x+"y"+y+"a",75*x,75*y);
				createState("x"+x+"y"+y+"b",75*x+30,75*y+30);
			}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");
		createLabel("d");
		createLabel("e");
		advanceToArcs();
		for(int x=0; x<size; x++) { createArc("x"+x+"y0a","b","x"+(x+1)+"y0a"); createArc("x"+x+"y0b","b","x"+(x+1)+"y0b"); }
		for(int y=0; y<size; y++) { createArc("x0y"+y+"a","a","x0y"+(y+1)+"a"); createArc("x0y"+y+"b","a","x0y"+(y+1)+"b"); }
		for(int x=0; x<size; x++)
			for(int y=0; y<size; y++) {
				createArc("x"+x+"y"+(y+1)+"a","b","x"+(x+1)+"y"+(y+1)+"a");
				createArc("x"+x+"y"+(y+1)+"b","b","x"+(x+1)+"y"+(y+1)+"b");
				createArc("x"+(x+1)+"y"+y+"a","a","x"+(x+1)+"y"+(y+1)+"a");
				createArc("x"+(x+1)+"y"+y+"b","a","x"+(x+1)+"y"+(y+1)+"b");
		}
		createArc("x"+size+"y"+size+"a","c","x0y0a");
		createArc("x"+size+"y"+size+"b","c","x0y0b");
		for(int x=0; x<=size; x++)
			for(int y=0; y<=size; y++) {
				createArc("x"+x+"y"+y+"a","d","x"+x+"y"+y+"b");
				createArc("x"+x+"y"+y+"b","e","x"+x+"y"+y+"a");
		}
	}

	public static void alternate(int size) {
		createInitialState("s0",0,0);
		for (int x=1; x<=size; x++) {
			createState("r"+x,75*x-75,100);
			createState("s"+x,75*x,0);
		}
		createState("r0",75*size,-100);
		advanceToLabels();
		createLabel("a");
		for (int x=0; x<=size; x++)
			createLabel("b"+x);
		advanceToArcs();
		for (int x=0; x<size; x++) createArc("s"+x,"a","r"+(x+1));
		createArc("s"+size,"a","r0");
		for (int x=0; x<=size; x++) createArc("r"+x,"b"+x,"s"+x);
	}

	public static void grid(int size) {
		for (int x=0; x<=size; x++)
			for (int y=0; y<=size; y++) {
				if (x==0 && y==0) createInitialState("x0y0",0,0);
				else createState("x"+x+"y"+y,75*x,75*y);
			}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for(int x=0; x<size; x++) createArc("x"+(x+1)+"y0","b","x"+x+"y0");
		for(int y=0; y<size; y++) createArc("x0y"+y,"a","x0y"+(y+1));
		for(int x=0; x<size; x++)
			for(int y=0; y<size; y++) {
				createArc("x"+x+"y"+(y+1),"b","x"+(x+1)+"y"+(y+1));
				createArc("x"+(x+1)+"y"+(y+1),"a","x"+(x+1)+"y"+y);
		}
	}

	public static void knobComb(int size) {
		for (int i=0; i<=size; i++) {
			if (i==0) createInitialState("s0",75,300);
			else createState("s"+i,(i+1)*75,300);
			createState("q"+i,(i+1)*75,200);
			createState("r"+i,(i+1)*75,100);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=0; i<=size; i++) {
			if (i<size) createArc("s"+i,"a","s"+(i+1));
			createArc("s"+i,"b","q"+i);
			createArc("q"+i,"b","r"+i,(i+1)*75+25,150);
			createArc("r"+i,"a","q"+i,(i+1)*75-25,150);
		}
	}

	public static void twig(int size) {
		int x=100, y=300;
		createInitialState("s0",x,y);
		for (int i=1; i<=size; i++) {
			x += 100;
			createState("q"+i,x,y-100);
			createState("r"+i,x,y);
			x += 100;
			createState("s"+i,x,y);
			createState("p"+i,x,y-200);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=0; i<size; i++) {
			createArc("s"+i,"a","r"+(i+1));
			createArc("s"+i,"b","q"+(i+1));
			createArc("r"+(i+1),"b","s"+(i+1));
			createArc("q"+(i+1),"a","p"+(i+1));
		}
	}

	public static void twig2(int size) {
		createInitialState("s0",75,75);
		for(int i=1; i<=size; i++) {
			createState("s"+i,75*(i+1),75);
			createState("r"+i,75*(i+1),150);
			if (i>2) createState("q"+i,75*(i+1),225);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=0; i<size; i++)
			if (i%2 == 0) { createArc("s"+i,"a","s"+(i+1)); 
					createArc("s"+i,"b","r"+(i+1));
					if (i>1) createArc("r"+i,"b","q"+(i+1));
			} else {	createArc("s"+i,"b","s"+(i+1));
					createArc("r"+i,"a","r"+(i+1));
					if (i>1) createArc("q"+i,"a","q"+(i+1));
			}
	}

	public static void cyclicPath(int size,boolean simple) {
		int x=100, y=100;
		createInitialState("s0",x,y);
		createState("r0",x,y+100);
		for(int i=1; i<=size; i++) {
			x += 100;
			createState("s"+i,x,y);
			createState("r"+i,x,y+100);
		}
		advanceToLabels();
		createLabel("c");
		createLabel("b");
		createLabel("a");
		advanceToArcs();
		for (int i=0; i<size; i++) {
			createArc("s"+i,"a","s"+(i+1));
			if (simple) {
				createArc("s"+(i+1),"c","r"+(i+1));
				createArc("r"+i,"b","r"+(i+1));
			} else {
				createArc("s"+i,(i%2==1?"b":"c"),"r"+i);
				createArc("r"+i,(i%2==1?"b":"c"),"r"+(i+1));
			}
		}
		if (simple) createArc("s0","b","r0");
		else createArc("s"+size,(size%2==1?"b":"c"),"r"+size);
	}

	public static void abcdTree(int size) {
		long step=90*(2<<(size-1)-1), x=50+(step+90)/2, y=200*size+50;
		int r=1, m=1;
		createInitialState("s0",x,y);
		for (int i=1; i<(2<<size)-1; i++) {
			if (--r==0) { m*=2; r=m; step/=2; x=50+(step+90)/2; y-=200; }
			else x+=step;
			createState("s"+i,x,y);
			createState("r"+i,x,y+100);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");
		createLabel("d");
		advanceToArcs();
		for (int i=0; i<(1<<size)-1; i++) {
			createArc("s"+i,(i%2==0?"a":"c"),"r"+(2*i+1));
			createArc("s"+i,(i%2==0?"b":"d"),"r"+(2*i+2));
			createArc("r"+(2*i+2),(i%2==0?"a":"c"),"s"+(2*i+2));
			createArc("r"+(2*i+1),(i%2==0?"b":"d"),"s"+(2*i+1));
		}
	}

	public static void abbaTree(int size) {
		long step=90*(2<<(size-1)-1), x=50+(step+90)/2, y=200*size+50;
		int r=1, m=1;
		createInitialState("s0",x,y);
		for (int i=1; i<(2<<size)-1; i++) {
			if (--r==0) { m*=2; r=m; step/=2; x=50+(step+90)/2; y-=200; }
			else x+=step;
			createState("r"+i,x,y+100);
			createState("s"+i,x,y);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=1; i<(2<<size)-1; i++) createArc("r"+i,(i%2==1 ? "b":"a"),"s"+i);
		for (int i=0; i<(1<<size)-1; i++) {
			createArc("s"+i,"a","r"+(2*i+1));
			createArc("s"+i,"b","r"+(2*i+2));
		}
	}

	public static void overlappingCycles(int size) {
		int x = 100;
		for (int i=0; i<=size; i++) {
			if (i==0) createInitialState("s0",x,100);
			else createState("s"+i,x,100);
			createState("r"+i,x,300);
			createState("q"+i,x+40,200);
			x += 100;
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");
		advanceToArcs();
		for (int i=0; i<=size; i++) {
			createArc("s"+i,"a","r"+i);
			createArc("s"+i,"c","q"+i);
			createArc("r"+i,"b","q"+i);
		}
		for (int i=0; i<size; i++) {
			createArc("s"+i,"b","s"+(i+1));
			createArc("r"+i,"c","r"+(i+1));
		}
	}

	public static void twoWayComb(int size) {
	// two combs with every 4th tooth missing
		for (int i=0; i<4*size+2; i++) {
			if (i==0) createInitialState("s0",(4*size+1)*75,100);
			else createState("s"+i,(4*size+1+i)*75,100);
			if (i%4 != 2) createState("r"+i,(4*size+1+i)*75,250); 
		}
		for (int i=4*size+2; i<8*size+3; i++) {
			createState("s"+i,75*(8*size+2-i),100);
                        if (i%4 != 3) createState("r"+i,75*(8*size+2-i),250);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");
		advanceToArcs();
		for (int i=0; i<4*size+1; i++) createArc("s"+i,"c","s"+(i+1)); 
		createArc("s0","a","s"+(4*size+2));
		for (int i=4*size+2; i<8*size+2; i++) createArc("s"+i,"a","s"+(i+1));
		for (int i=0; i<4*size+2; i++)
			if (i%4 != 2) createArc("s"+i,"b","r"+i); 
		for (int i=4*size+2; i<8*size+3; i++) 
			if (i%4 != 3) createArc("s"+i,"b","r"+i);
	}

	public static void staticComb(int size) {
	// comb with every 6th tooth missing
		for (int i=0; i<6*size+5; i++) {
			if (i==0) createInitialState("s0",i*75,100);
			else createState("s"+i,i*75,100);
			if (i%6 < 5) createState("r"+i,i*75,250);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=0; i<6*size+4; i++) createArc("s"+i,"a","s"+(i+1));
		for (int i=0; i<6*size+5; i++)
			if (i%6 < 5) createArc("s"+i,"b","r"+i);
	}

	public static void linearComb(int size) {
	// comb with one missing tooth in the middle
		for (int i=0; i<2*size+1; i++) {
			if (i==0) createInitialState("s0",i*75,100);
			else createState("s"+i,i*75,100);
			if (i!=size) createState("r"+i,i*75,250);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=0; i<2*size; i++) createArc("s"+i,"a","s"+(i+1));
		for (int i=0; i<2*size+1; i++) 
			if (i!=size) createArc("s"+i,"b","r"+i);
	}

	public static void quadraticComb(int size) {
	// comb (n teeth, then one missing), repeated n times, and finally n teeth
		for (int i=0; i<(size+2)*size; i++) {
			if (i==0) createInitialState("s0",i*75,100);
			else createState("s"+i,i*75,100);
			if ((i+1)%(size+1)!=0) createState("r"+i,i*75,250);
		}
		advanceToLabels();
		createLabel("a");
		createLabel("b");
		advanceToArcs();
		for (int i=0; i<(size+2)*size-1; i++) createArc("s"+i,"a","s"+(i+1));
		for (int i=0; i<(size+2)*size; i++) 
			if ((i+1)%(size+1)!=0) createArc("s"+i,"b","r"+i);
	}

	static void generateCycle(int numCycles, int sizeCycle) {
		long shift = numCycles * 100 + 50;
		for (int cycle = 0; cycle < numCycles; cycle++) {
			for (int state = 0; state < sizeCycle; state++) {
				String name = String.format("c%ds%d", cycle, state);
				double angle = -2 * Math.PI * (0.25 + state * 1.0 / sizeCycle);
				double distance = (cycle + 1) * 100;
				long x = shift + (long) (distance * Math.sin(angle));
				long y = shift + (long) (distance * Math.cos(angle));
				if (state == 0 && cycle == numCycles - 1)
					createInitialState(name, x, y);
				else
					createState(name, x, y);
			}
		}

		advanceToLabels();
		createLabel("a");
		createLabel("b");
		createLabel("c");

		advanceToArcs();
		for (int cycle = 0; cycle < numCycles; cycle++) {
			for (int state = 0; state < sizeCycle; state++) {
				String name = String.format("c%ds%d", cycle, state);

				// Edge inside the cycle
				createArc(name, "a", String.format("c%ds%d", cycle, (state + 1) % sizeCycle));

				// Edge to the outer cycle
				if (cycle + 1 < numCycles) {
					createArc(name, "b", String.format("c%ds%d", cycle + 1, (state + 1) % sizeCycle));
				}

				// Edge to the inner cycle
				if (cycle > 0) {
					createArc(name, "c", String.format("c%ds%d", cycle - 1, state));
				}
			}
		}
	}

	public static void createState(String state, long x, long y) {
		System.out.println(state+"[properties=\"pos "+x+","+y+"\"]");
	}

	public static void createInitialState(String state, long x, long y) {
		System.out.println(state+"[initial=\"true\", properties=\"pos "+x+","+y+"\"]");
	}

	public static void advanceToLabels() {
		System.out.println("\n.labels");
	}

	public static void createLabel(String label) {
		System.out.println(label);
	}

	public static void advanceToArcs() {
		System.out.println("\n.arcs");
	}

	public static void createArc(String st1, String lab, String st2) {
		System.out.println(st1+" "+lab+" "+st2);
	}

	public static void createArc(String st1, String lab, String st2, int x, int y) {
		System.out.println(st1+" "+lab+" "+st2+"[properties=\"bp "+x+","+y+"\"]");
	}
}
