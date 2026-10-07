module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} {Λ : Type v} [CommRing Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [hXTensor :
    @DerivedTensor.Right.Has (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) _ _ _ _ _ _]
variable [hYTensor :
    @DerivedTensor.Right.Has (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) _ _ _ _ _ _]

/-- Lemma 59.96.6: if `f : X ⟶ Y` is a proper morphism of schemes and `Λ` is a
torsion ring, then for `E` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)`,
`Rf_* E ⊗ᴸ K` is isomorphic in `D(Y_étale, Λ)` to `Rf_*(E ⊗ᴸ f⁻¹ K)`.
The source identification is this isomorphism; the unnamed canonical arrow
is the Section 21.50 left projection-formula mate. -/
@[stacks 0F0G]
theorem etalePushforwardDerived_tensor_inverseImage_of_isProper
    (f : X ⟶ Y) [IsProper f]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]
    [PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]
    (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) :
    Nonempty
      ((RightDerived.Cochain.functor
            ((smallEtalePullback f).sheafPushforwardContinuous
              (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)).obj E ⊗ᴸ K ≅
        (RightDerived.Cochain.functor
            ((smallEtalePullback f).sheafPushforwardContinuous
              (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology)).obj
          (E ⊗ᴸ
            (((smallEtalePullback f).sheafPullback
                (ModuleCat.{v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory.obj
              K))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
