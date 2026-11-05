/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a categorically flat module sheaf is a flat module. Tensoring
its stalk identifies with constant sheaf, tensor by the sheaf, then the fibre;
all three functors preserve finite limits. -/
theorem flat_sheafFiber_of_isFlat
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [(X.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    [CategoryTheory.MonoidalCategory.IsFlat F]
    (point : CategoryTheory.GrothendieckTopology.Point.{u} X.smallEtaleTopology) :
    Module.Flat Λ ((point.sheafFiber (A := ModuleCat.{u} Λ)).obj F) := by
  letI : ∀ M : ModuleCat.{u} Λ, CategoryTheory.Limits.PreservesColimits
      (CategoryTheory.MonoidalCategory.tensorRight M) := fun M =>
    CategoryTheory.Limits.preservesColimits_of_natIso
      (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight M)
  let L := constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)
  let P := point.sheafFiber (A := ModuleCat.{u} Λ)
  letI : CategoryTheory.Limits.PreservesFiniteLimits L :=
    CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  letI : CategoryTheory.Limits.PreservesFiniteLimits
      (L ⋙ CategoryTheory.MonoidalCategory.tensorRight F ⋙ P) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  let e : L ⋙ CategoryTheory.MonoidalCategory.tensorRight F ⋙ P ≅
      CategoryTheory.MonoidalCategory.tensorRight (P.obj F) :=
    (Functor.isoWhiskerLeft L (Functor.Monoidal.commTensorRight P F)).symm ≪≫
      Functor.isoWhiskerRight (point.constantSheafCompFiberIso)
        (CategoryTheory.MonoidalCategory.tensorRight (P.obj F))
  exact (Module.Flat.iff_preservesFiniteLimits_tensorRight (P.obj F)).mpr
    (CategoryTheory.Limits.preservesFiniteLimits_of_natIso e)

/-- The geometric stalk complex of an étale module sheaf complex is obtained by applying the
canonical geometric fiber functor to its terms and differentials. -/
def moduleStalkComplex {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (geometricPoint : Spec (.of Ω) ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ) :
    CochainComplex (ModuleCat.{u} Λ) ℤ :=
  ((Scheme.pointSmallEtale geometricPoint).sheafFiber.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- An étale module sheaf is stalkwise flat if its canonical fiber at every algebraically
closed field-valued geometric point is a flat module. -/
def IsStalkwiseFlatModule (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X),
    Module.Flat Λ
      (((Scheme.pointSmallEtale geometricPoint).sheafFiber (A := ModuleCat.{u} Λ)).obj F)

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- The geometric stalk of an étale sheaf of modules is its canonical site-point fiber
in the category of modules. -/
noncomputable def étaleModuleStalk (sbar : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ModuleCat.{u} Λ :=
  (GeometricPoint.toSmallEtalePoint sbar).presheafFiber.obj F.obj

/-- The underlying type of a geometric module stalk is equivalent to the geometric stalk
of the sheaf obtained by forgetting the module structure. -/
noncomputable def étaleModuleStalk_forget (sbar : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))] :
    (CategoryTheory.forget (ModuleCat.{u} Λ)).obj (étaleModuleStalk sbar F) ≃
      Scheme.Etale.stalk sbar
        ((sheafCompose S.smallEtaleTopology
            (CategoryTheory.forget (ModuleCat.{u} Λ))).obj F).obj :=
  (preservesColimitIso (CategoryTheory.forget (ModuleCat.{u} Λ))
      ((CategoryOfElements.π (GeometricPoint.toSmallEtalePoint sbar).fiber).op ⋙
        F.obj)).toEquiv

end AlgebraicGeometry.Scheme
