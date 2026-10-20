/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Relative
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom complexes after pushout base change

This leaf owns the termwise-flat consequence of changing a finite-projective Hom model around a
pushout square of rings.  It stays below the derived-category layer: no monoidal or localization
structure is needed to state a property of the resulting cochain complex.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

namespace CochainComplex.HomComplex.Pushout

variable {R A R' A' : Type u}
variable [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
variable [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
variable [IsScalarTower R A A'] [IsScalarTower R R' A']
variable [hpush : Algebra.IsPushout R R' A A']

include hpush

/-- A pushout base change carries the relatively flat, bounded Hom model to a complex that is
termwise flat over the new base ring.  The finite-projective source is the precise hypothesis that
makes each Hom term a finite sum of target terms. -/
@[stacks 0E1U "termwise flatness of a pushout Hom model"]
theorem isTermwiseFlatOver
    (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    ((CochainComplex.HomComplex.ScalarExtension.functor (algebraMap A A')).obj
      (CochainComplex.HomComplex.moduleComplex A P F)).IsTermwiseFlatOver R' := sorry
/- Proof strategy: apply the generic Hom-complex flatness theorem over `R`, then transport each
finite support term through `Algebra.IsPushout.cancelBaseChange`. -/

end CochainComplex.HomComplex.Pushout
