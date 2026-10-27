/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Resolution
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (B : CochainDGAlgebra.{u, v} R)

/-!
# Lemma 22.38.1 (0BZ7)

The source replacement is owned by
`CochainDGAlgebra.Free.KFlatResolution`: it packages the resolving DGA, its
free graded-algebra presentation, K-flatness, and the quasi-isomorphism to the
target. No partial generator-adjoining constructor is exposed.
-/

/- The unrestricted source-facing statement uses the actual carrier lift.  The resolving
carrier and its word basis therefore live in `max u v`, while the coefficient ring and the
original DGA remain the given `R` and `B`. -/
@[stacks 0BZ7]
theorem lemma_22_38_1 :
    Nonempty (CochainDGAlgebra.Free.KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) :=
  CochainDGAlgebra.Free.KFlatResolution.nonempty_unrestricted B

/- This is the concrete comparison retained by the facade.  Its degreewise components are the
canonical `ULift.up` equivalences, so cohomology comparisons can use the faithful carrier lift. -/
@[stacks 061X]
def lemma_22_38_1_comparison :
    CochainDGAlgebra.Hom B (CochainDGAlgebra.ulift.{u, v, u} B) :=
  CochainDGAlgebra.Free.KFlatResolution.uliftComparison B

@[stacks 061X]
theorem lemma_22_38_1_comparison_component (n : ℤ) :
    (lemma_22_38_1_comparison B).map n =
      (CochainDGAlgebra.Free.KFlatResolution.uliftComparisonEquiv B n).toLinearMap := rfl

@[simp, stacks 061X]
theorem lemma_22_38_1_comparison_apply (n : ℤ) (x : B.X n) :
    (lemma_22_38_1_comparison B).map n x = ULift.up x := rfl

/- For a selected lifted resolution `P`, the source-facing comparison to the original `B` is
the heterogeneous map obtained by lowering only the target component. -/
@[stacks 061X]
def lemma_22_38_1_lowered_comparison
    (P : CochainDGAlgebra.Free.KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) :
    CochainDGAlgebra.Hom P.complex B :=
  CochainDGAlgebra.Free.KFlatResolution.lowerComparison P

@[stacks 061X]
theorem lemma_22_38_1_lowered_comparison_apply
    (P : CochainDGAlgebra.Free.KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) (n : ℤ) (x : P.complex.X n) :
    (lemma_22_38_1_lowered_comparison B P).map n x = (P.π.map n x).down := rfl

@[stacks 061X]
theorem lemma_22_38_1_lowered_comparison_quasiIso
    (P : CochainDGAlgebra.Free.KFlatResolution.{u, max u v, max u v}
      (CochainDGAlgebra.ulift.{u, v, u} B)) :
    CochainDGAlgebra.quasiIso
      (CochainDGAlgebra.Free.KFlatResolution.lowerComparisonLift P) :=
  CochainDGAlgebra.Free.KFlatResolution.lowerComparisonLift_quasiIso P
