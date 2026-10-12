/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

variable {X Y : Scheme.{u}}
variable [MonoidalCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (ComplexShape.up ℤ)]
variable [hXTensor :
    @DerivedTensor.Right.Has (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) _ _ _ _ _ _]
variable [MonoidalCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [MonoidalPreadditive (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})) (ComplexShape.up ℤ)]
variable [hYTensor :
    @DerivedTensor.Right.Has (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) _ _ _ _ _ _]

/-- Lemma 59.92.5: if `f : X ⟶ Y` is a proper morphism of schemes,
`E ∈ D⁺(X_étale)` has torsion cohomology sheaves, and `K ∈ D⁺(Y_étale)`,
then `Rf_* E ⊗ᴸ K ≅ Rf_*(E ⊗ᴸ f⁻¹ K)` in `D(Y_étale)` after `Plus.ι`.
The source identification is this isomorphism; the unnamed canonical
arrow is the Section 21.50 left projection-formula mate. -/
@[stacks 0F0F]
theorem etaleDerivedPushforward_tensor_inverseImage
    (f : X ⟶ Y) [IsProper f]
    [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (abelianPushforwardAlong f))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})) :
    Nonempty
      (DerivedTensor.Right.obj
          (DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward f).obj E))
          (DerivedCategory.Plus.ι.obj K) ≅
        (RightDerived.Cochain.functor (abelianPushforwardAlong f)).obj
          (DerivedTensor.Right.obj
            (DerivedCategory.Plus.ι.obj E)
            (DerivedCategory.Plus.ι.obj ((etaleDerivedInverseImage f).obj K)))) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
