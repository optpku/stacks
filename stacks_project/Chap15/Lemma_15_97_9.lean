/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition.Homology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.9: eta decomposition and its Bockstein locus

The Bockstein vanishing locus, total eta decomposition ideal,
its quotient, and the five source conclusions are exposed through their reusable ReasLib owners.
The finite-presentation conclusion is split into its surjectivity and finite-presentation parts.

@stack 0F81
-/

#check @HomologicalComplex.Bockstein.cyclesLiftLocus
#check @HomologicalComplex.Bockstein.operatorZeroLocus
@[stacks 0F81 "cycles lifting equals localized Bockstein vanishing"]
#check @HomologicalComplex.Bockstein.cyclesLiftLocus_eq_operatorZeroLocus

#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.ideal
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.Quotient
@[stacks 0F81 "(1) finite generation of the total decomposition ideal"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.ideal_fg
@[stacks 0F81 "(2a) surjectivity of the decomposition quotient map"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.quotientMap_surjective
@[stacks 0F81 "(2b) finite presentation of the decomposition quotient"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.quotient_finitePresentation
@[stacks 0F81 "(3) local vanishing of the total decomposition ideal"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.localizedIdeal_eq_bot_of_mem_cyclesLiftLocus
@[stacks 0F81 "(4) localized free cohomology lies in the Bockstein locus"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.mem_cyclesLiftLocus_of_localizedHomology_free
@[stacks 0F81 "(5) finite locally free eta cohomology"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.homology_finiteLocallyFree
