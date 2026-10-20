/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat R) (ZMod 2))

/- A general `2`-periodic complex over `R` is a cochain complex of
`R`-modules indexed by `ZMod 2`; its two differentials have zero composites. -/
#check (CochainComplex (ModuleCat R) (ZMod 2) : Type _)

#check @CochainComplex.of
#check @HomologicalComplex.d_comp_d

/- Its cohomology objects in degrees `0` and `1` are canonically
the kernels of the outgoing differentials modulo the images of the incoming differentials. -/
#check (K.sc (0 : ZMod 2)).moduleCatHomologyIso
#check (K.sc (1 : ZMod 2)).moduleCatHomologyIso

/- Exactness of a `2`-periodic complex means degreewise exactness,
equivalently vanishing of its two cohomology objects. -/
#check (K.Acyclic : Prop)

#check @HomologicalComplex.exactAt_iff_isZero_homology

/- Definition 42.2.1: a `(2, 1)`-periodic complex is the special case with the same
`R`-module in both degrees and two endomorphism differentials. -/
@[stacks 02PG] #check
  (CategoryTheory.TwoPeriodicEndomorphism (ModuleCat R) : Type _)

#check @CategoryTheory.TwoPeriodicEndomorphism.toCochainComplex

#check @CategoryTheory.TwoPeriodicEndomorphism.toCochainComplex_X
#check @CategoryTheory.TwoPeriodicEndomorphism.toCochainComplex_d_zero
#check @CategoryTheory.TwoPeriodicEndomorphism.toCochainComplex_d_one

end
