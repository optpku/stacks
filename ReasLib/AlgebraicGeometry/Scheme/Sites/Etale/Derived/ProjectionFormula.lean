module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.GroupTheory.Torsion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

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
variable [((X.smallEtaleTopology.W :
    MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [((Y.smallEtaleTopology.W :
    MorphismProperty (Y.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [hXTensor :
    DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [hYTensor :
    DerivedTensor.Right.Has (C := Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- For a proper morphism of schemes and a torsion commutative coefficient ring, derived
pushforward on étale module sheaves satisfies the projection formula for arbitrary unbounded
derived objects. -/
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

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [((X.smallEtaleTopology.W :
    MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ)))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [((Y.smallEtaleTopology.W :
    MorphismProperty (Y.Etaleᵒᵖ ⥤ ModuleCat.{u} (ULift.{u} ℤ)))).IsMonoidal]
variable [MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))) (ComplexShape.up ℤ)]
variable [∀ (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))) (ComplexShape.up ℤ)]
variable [hXTensor :
    DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [hYTensor :
    DerivedTensor.Right.Has (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))]
variable [X.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})]

/-- For a proper morphism of schemes, a bounded-below étale complex with locally torsion
cohomology satisfies the derived projection formula against every bounded-below étale complex.
Both the tensor with inverse image and the tensor of derived pushforward are bounded below.
The coefficient ring `ULift ℤ` represents integer coefficients via `ULift.ringEquiv`. -/
theorem etaleDerivedPushforward_tensor_inverseImage
    (f : X ⟶ Y) [IsProper f]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) (ComplexShape.up ℤ))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f).sheafPullback
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)]
    [PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback
        (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))))
    (hE : ∀ i : ℤ,
      IsLocallyTorsion
        ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u})).obj
          ((DerivedCategory.Plus.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ))) i).obj E)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ULift.{u} ℤ)))) :
    (∃ n : ℤ,
      (DerivedCategory.Plus.ι.obj E ⊗ᴸ
        ((smallEtalePullback f).sheafPullback
          (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj K)).IsGE n) ∧
    (∃ n : ℤ,
      ((RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)).obj
              (DerivedCategory.Plus.ι.obj E) ⊗ᴸ DerivedCategory.Plus.ι.obj K).IsGE n) ∧
    Nonempty
      ((RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)).obj
              (DerivedCategory.Plus.ι.obj E) ⊗ᴸ DerivedCategory.Plus.ι.obj K ≅
        (RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology)).obj
          (DerivedCategory.Plus.ι.obj E ⊗ᴸ
            ((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} (ULift.{u} ℤ)) Y.smallEtaleTopology X.smallEtaleTopology).mapDerivedCategory.obj
                (DerivedCategory.Plus.ι.obj K))) := sorry

end AlgebraicGeometry.Scheme.Hom

end
