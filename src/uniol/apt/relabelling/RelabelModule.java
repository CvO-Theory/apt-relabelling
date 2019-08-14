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

import uniol.apt.adt.pn.PetriNet;
import uniol.apt.adt.ts.State;
import uniol.apt.adt.ts.TransitionSystem;
import uniol.apt.analysis.synthesize.AbstractSynthesizeModule;
import uniol.apt.analysis.synthesize.AbstractSynthesizeModule.Options;
import uniol.apt.analysis.synthesize.PNProperties;
import uniol.apt.module.AbstractModule;
import uniol.apt.module.AptModule;
import uniol.apt.module.Category;
import uniol.apt.module.InterruptibleModule;
import uniol.apt.module.ModuleInput;
import uniol.apt.module.ModuleInputSpec;
import uniol.apt.module.ModuleOutput;
import uniol.apt.module.ModuleOutputSpec;
import uniol.apt.module.exception.ModuleException;
import java.util.Collections;
import java.util.Collection;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * @author Harro Wimmel
 *
 */
@AptModule
public class RelabelModule extends AbstractModule implements InterruptibleModule {

	@Override
	public String getName() {
		return "relabel";
	}

//	static String getOptionsDescription(String extraOptions, String extraOptionsDescriptions) {
	@Override
	public String getLongDescription() {
		return getShortDescription() + ".\n"
			+ " Supported options are: essp, ssp, all, base, tree, order, time,\n"
			+ "                        quick-fail, and verbose.\n"
			+ " \nThe meaning of these options is as follows:\n"
			+ " - essp: The lts is made deterministic and all ESSP problems are solved.\n"
			+ "   This includes SSP problems induced by ESSP problems.\n"
			+ " - ssp: The lts is made deterministic and all SSP problems are solved.\n"
			+ " - all: The options essp and ssp together.\n"
			+ " - base: The chord vectors are condensed to a basis.\n"
			+ " - tree: The spanning tree is breadth-first, but otherwise arbitrary.\n"
			+ "         (Normally, it is made breadth-first and extra shallow.)\n"
			+ " - order: For 'all' SSP and ESSP are swapped in order (ESSP handled early).\n"
			+ " - time: The elapsed time is printed to stdout.\n"
			+ " - quick-fail (qf): If the lts is not totally reachable, the module stops.\n"
			+ "   prematurely.\n"
			+ " - verbose (vb): Print details about the renaming process.\n"
			+ "Without options ssp/essp/all the lts will just be made deterministic.\n"
			+ "Primary output is a new lts where some event labels are renamed.\n"
			+ "Failure is possible if and only if there are unreachable states.\n";
	}


	@Override
	public void require(ModuleInputSpec inputSpec) {
		inputSpec.addParameter("lts", TransitionSystem.class, "The LTS that should be examined");
//		inputSpec.addParameter("bound", Long.class, "The bound k for the net (0=unspecified)");
		inputSpec.addOptionalParameterWithDefault("options", String.class, "vb", "verbose", "Comma separated list of options");
	}

	@Override
	public void provide(ModuleOutputSpec outputSpec) {
		outputSpec.addReturnValue("result", Boolean.class, "result",
				ModuleOutputSpec.PROPERTY_SUCCESS);
		outputSpec.addReturnValue("ts_out", TransitionSystem.class,
				ModuleOutputSpec.PROPERTY_FILE, ModuleOutputSpec.PROPERTY_RAW);
	}

	@Override
	public void run(ModuleInput input, ModuleOutput output) throws ModuleException {
		TransitionSystem ts = input.getParameter("lts", TransitionSystem.class);

		String quickFailStr = "quick-fail", verboseStr = "verbose", qfStr = "qf", vbStr = "vb";
		Set<String> supportedExtraOptions = new HashSet<>(Arrays.asList(quickFailStr, qfStr, verboseStr, vbStr));
		Collection<String> SSPSynthStr = Arrays.asList("SSP", "ssp", "state");
		supportedExtraOptions.addAll(SSPSynthStr);
		Collection<String> ESSPSynthStr = Arrays.asList("ESSP", "essp", "event");
		supportedExtraOptions.addAll(ESSPSynthStr);
		Collection<String> ALLSynthStr = Arrays.asList("ALL", "all");
		supportedExtraOptions.addAll(ALLSynthStr);
		Collection<String> timeSynthStr = Arrays.asList("time", "TIME");
		supportedExtraOptions.addAll(timeSynthStr);
		Collection<String> orderStr = Arrays.asList("delayssp","esspfirst","order");
		supportedExtraOptions.addAll(orderStr);
		Collection<String> baseStr = Arrays.asList("truebase","base");
		supportedExtraOptions.addAll(baseStr);
		Collection<String> treeStr = Arrays.asList("tree","simpletree","deeptree");
		supportedExtraOptions.addAll(treeStr);

		Options options = Options.parseProperties(input.getParameter("options", String.class),
				supportedExtraOptions);
		boolean quickFail = options.extraOptions.contains(quickFailStr) || options.extraOptions.contains(qfStr);
		boolean verbose = options.extraOptions.contains(verboseStr) || options.extraOptions.contains(vbStr);
		boolean ssp = !Collections.disjoint(options.extraOptions, SSPSynthStr);
		boolean essp = !Collections.disjoint(options.extraOptions, ESSPSynthStr);
		if (!Collections.disjoint(options.extraOptions, ALLSynthStr)) {
			essp = true;
			ssp = true;
		}
		boolean time = !Collections.disjoint(options.extraOptions, timeSynthStr);
		boolean delayssp = !Collections.disjoint(options.extraOptions, orderStr);
		boolean truebase = !Collections.disjoint(options.extraOptions, baseStr);
		boolean shallowtree = Collections.disjoint(options.extraOptions, treeStr);

		Relabel RL = new Relabel(ts, options.properties, quickFail, ssp, essp, time, delayssp, truebase, shallowtree);

		output.setReturnValue("result", Boolean.class, RL.getResult());
		output.setReturnValue("ts_out", TransitionSystem.class, RL.getTS());
	}

	@Override
	public String getShortDescription() {
		return "Renaming of Events for Labelled Synthesis of LTS";
	}

	@Override
	public Category[] getCategories() {
		return new Category[]{Category.LTS};
	}
}

