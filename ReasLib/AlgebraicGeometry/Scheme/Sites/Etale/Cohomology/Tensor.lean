/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open scoped GrothendieckTopologyDerivedSections
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [MonoidalCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [MonoidalPreadditive (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [MonoidalCategory AddCommGrpCat.{u}]
variable [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (ComplexShape.up ℤ)]
variable [MonoidalPreadditive AddCommGrpCat.{u}]
variable [∀ (K L : CochainComplex AddCommGrpCat.{u} ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor AddCommGrpCat.{u}) (ComplexShape.up ℤ)]
variable [hSheafTensor :
    @DerivedTensor.Right.Has (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) _ _ _ _ _ _]
variable [hAbTensor : @DerivedTensor.Right.Has AddCommGrpCat.{u} _ _ _ _ _ _]
variable [(constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).Additive]
variable [PreservesFiniteLimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [PreservesFiniteColimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable
  [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- The image of `K ∈ D⁺(ℤ)` under the derived constant sheaf functor on `X_étale`.
The ambient `MonoidalCategory` on `AddCommGrpCat` is the tensor of abelian groups
`⊗_ℤ`; it is not the cartesian product monoidal structure. -/
noncomputable def underlineDerived
    (X : Scheme.{u}) [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [(constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).Additive]
    [PreservesFiniteLimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [PreservesFiniteColimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (K : DerivedCategory.Plus AddCommGrpCat.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).mapDerivedCategory.obj
    (DerivedCategory.Plus.ι.obj K)

/-- Derived étale global sections commute with tensoring by the derived constant
sheaf of a bounded-below complex of abelian groups. -/
theorem rGamma_tensor_constant
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (K : DerivedCategory.Plus AddCommGrpCat.{u}) :
    Nonempty
      ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj
          (DerivedTensor.Right.obj (DerivedCategory.Plus.ι.obj E)
            (underlineDerived X K)) ≅
        DerivedTensor.Right.obj
          ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj
            (DerivedCategory.Plus.ι.obj E))
          (DerivedCategory.Plus.ι.obj K)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
