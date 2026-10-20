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
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

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
