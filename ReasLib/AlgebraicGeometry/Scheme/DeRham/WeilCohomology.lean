/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Functor
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Correspondence
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.ChowGroup.FieldFundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] [CharZero k]

/-- A classical theory realizes relative de Rham cohomology when its comparisons in every
cohomological degree and Tate twist preserve canonical pullback, the constant-one class,
wedge cup products, and Tate trivialization. Its integral Chow operations are
identified by the theory's uniform geometric Chow comparison. -/
def RealizesCohomology (T : WeilCohomology.SchemeClassicalTheory.Object k k) : Prop :=
  letI : ∀ X, GradedAlgebra (T.Hgrade X) := T.hHgrade
  letI : ∀ X, GradedAlgebra (T.CHgrade X) := T.hCHgrade
  (let S := T.theory.scheme
   ∃ (comparison : ∀ (X : T.V) (i n : ℤ),
        T.theory.twistedGrade X i n ≃ₗ[k]
          cohomologyOverAffineBase (A := CommRingCat.of k) (S.obj X).hom i)
      (tate : T.TateLine ≃ₗ[k] k),
     (∀ (X Y : T.V) (f : X ⟶ Y) (i n : ℤ)
        (a : T.theory.twistedGrade Y i n),
       ((WeilCohomology.Tate.trivialization T.theory.tateLine_rank (T.Hgrade X i) n)
          ((comparison X i n).symm
            ((Cohomology.pullbackOverField (k := k) (X := S.obj X) (Y := S.obj Y)
              (S.map f) i).hom (comparison Y i n a))) : T.H X) =
         T.theory.pullback f
           ((WeilCohomology.Tate.trivialization T.theory.tateLine_rank (T.Hgrade Y i) n) a)) ∧
     (∀ X,
       ((WeilCohomology.Tate.trivialization T.theory.tateLine_rank (T.Hgrade X 0) 0)
         ((comparison X 0 0).symm
           (ClassAction.cohomologyOneCanonical (S.obj X).hom)) : T.H X) = 1) ∧
     (∀ X i i' n n' (a : T.theory.twistedGrade X i n)
        (b : T.theory.twistedGrade X i' n'),
       ((WeilCohomology.Tate.trivialization T.theory.tateLine_rank
           (T.Hgrade X (i + i')) (n + n'))
         ((comparison X (i + i') (n + n')).symm
           ((CanonicalAction.cupMorphism (S.obj X).hom i i').hom
             (TensorProduct.tmul (coefficientRing (S.obj X).hom)
               (comparison X i n a) (comparison X i' n' b)))) : T.H X) =
       ((WeilCohomology.Tate.trivialization T.theory.tateLine_rank (T.Hgrade X i) n) a : T.H X) *
         ((WeilCohomology.Tate.trivialization T.theory.tateLine_rank (T.Hgrade X i') n') b : T.H X)) ∧
     (∀ X i n (a : T.theory.twistedGrade X i n) (t : T.TateLine),
       comparison X i (n + 1) (T.theory.tateTwist X i n (TensorProduct.tmul k a t)) =
         tate t • comparison X i n a))

/-- Over a characteristic-zero field, the canonical graded relative de Rham functor
admits a classical Weil cohomology structure with its canonical operations. -/
theorem existsWeilTheory (k : Type u) [Field k] [CharZero k] :
    ∃ T : WeilCohomology.SchemeClassicalTheory.Object k k,
      T.IsWeil ∧ RealizesCohomology T := by
  sorry

end AlgebraicGeometry.Scheme.DeRham
