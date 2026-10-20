/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Homology

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open Opposite
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open scoped Simplicial
open scoped IteratedEndofunctor

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.Homology

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A B : Sheaf J CommRingCat.{u}}

/-- The sheaf-level cotangent complex of a homomorphism of sheaves of rings. -/
abbrev cotangentComplex (φ : A ⟶ B) :
    CochainComplex (SheafOfModules (ringSheaf J B)) ℤ :=
  SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)

/-- Evaluation of sheaves of `B`-modules on an object of the site. -/
abbrev eval (X : Cᵒᵖ) :
    SheafOfModules.{u} (ringSheaf J B) ⥤ ModuleCat.{u} ((ringSheaf J B).obj.obj X) :=
  SheafOfModules.evaluation.{u} (ringSheaf J B) X

#check (SheafOfModules.RingedSite.CotangentComplex.Homology.sectionsComplexMap :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (X : Cᵒᵖ),
    RingHom.cotangentComplex (φ.hom.app X).hom ⟶
      ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)))

end SheafOfModules.RingedSite.CotangentComplex.Homology
