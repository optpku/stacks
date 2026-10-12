/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.Torsion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable {Λ : Type v} [CommRing Λ]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [((X.smallEtaleTopology.W :
    MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (ModuleCat.{v} Λ)]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [∀ (K L : CochainComplex (ModuleCat.{v} Λ) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ModuleCat.{v} Λ)) (ComplexShape.up ℤ)]
variable [hSheafTensor : DerivedTensor.Right.Has
  (C := Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [hModTensor : DerivedTensor.Right.Has (C := ModuleCat.{v} Λ)]
variable [(constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
    (op (globalEtale X))).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
        (op (globalEtale X))))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]

/-- The derived global sections of a tensor with a constant module complex satisfy the projection
formula for a quasi-compact quasi-separated scheme of finite étale cohomological dimension. -/
theorem rGamma_tensor_constant_module
    (hcd : cohomologicalDimension X ≠ ⊤)
    (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (ModuleCat.{v} Λ)) :
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
              (op (globalEtale X)))).obj
          (E ⊗ᴸ
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ)).mapDerivedCategory.obj K)) ≅
        ((RightDerived.Cochain.functor
            ((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
              (op (globalEtale X)))).obj E) ⊗ᴸ
          K) := sorry

end AlgebraicGeometry.Scheme.Etale

end
