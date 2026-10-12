/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_18_4_Homology
public import Mathlib.Algebra.Homology.Additive

/-!
# Objectwise sections of the ring-sheaf cotangent complex

This module owns the rule `U ↦ L(B(U)/A(U))` as a cochain complex of `B`-module
presheaves, together with its sheafification and the canonical comparison to `L(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.Sections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A B : Sheaf J CommRingCat.{u}}

/-- Restriction of the evaluated sheaf cotangent complex along a morphism of the site. -/
def evalRestrict (φ : A ⟶ B) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((Homology.eval X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Homology.cotangentComplex φ) ⟶
      ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Homology.eval Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Homology.cotangentComplex φ)) where
  f i := ((Homology.cotangentComplex φ).X i).val.map f
  comm' := sorry

/-- The cochain complex of `B`-module presheaves with value `U ↦ L(B(U)/A(U))`. -/
def complex (φ : A ⟶ B) :
    CochainComplex (PresheafOfModules (ringSheaf J B).obj) ℤ where
  X i :=
    { obj U := (RingHom.cotangentComplex (φ.hom.app U).hom).X i
      map f := (Homology.complexMap φ f).f i
      map_id := sorry
      map_comp := sorry }
  d i j :=
    { app U := (RingHom.cotangentComplex (φ.hom.app U).hom).d i j
      naturality := sorry }
  shape := sorry
  d_comp_d' := sorry

/-- Unfolding of the objectwise value of `complex`. -/
theorem complex_X (φ : A ⟶ B) (i : ℤ) (U : Cᵒᵖ) :
    ((complex φ).X i).obj U = (RingHom.cotangentComplex (φ.hom.app U).hom).X i :=
  sorry

/-- The morphism of complexes of `B`-module presheaves sending `U ↦ L(B(U)/A(U))` to
the underlying presheaf complex of `L(φ)`. -/
def presheafComparison (φ : A ⟶ B) :
    complex φ ⟶
      ((PresheafOfModules.restrictScalars (𝟙 (ringSheaf J B).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.forget (ringSheaf J B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (Homology.cotangentComplex φ)) where
  f i :=
    { app U := (Homology.sectionsComplexMap φ U).f i
      naturality := sorry }
  comm' := sorry

/-- Unfolding of the components of `presheafComparison` on an object of the site. -/
theorem presheafComparison_f_app (φ : A ⟶ B) (i : ℤ) (U : Cᵒᵖ) :
    ((presheafComparison φ).f i).app U = (Homology.sectionsComplexMap φ U).f i :=
  sorry

/-- The sheafification of the rule `U ↦ L(B(U)/A(U))`, as a complex of sheaves of
`B`-modules. -/
def sheafify (φ : A ⟶ B) :
    CochainComplex (SheafOfModules (ringSheaf J B)) ℤ where
  X i :=
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj ((complex φ).X i)
  d i j :=
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).map ((complex φ).d i j)
  shape := sorry
  d_comp_d' := sorry

/-- Unfolding of the terms of `sheafify`. -/
theorem sheafify_X (φ : A ⟶ B) (i : ℤ) :
    (sheafify φ).X i =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj ((complex φ).X i) :=
  sorry

/-- The canonical comparison from the sheafification of `U ↦ L(B(U)/A(U))` to `L(φ)`. -/
def comparison (φ : A ⟶ B) : sheafify φ ⟶ Homology.cotangentComplex φ where
  f i :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).symm
      ((presheafComparison φ).f i)
  comm' := sorry

/-- The comparison morphism is the sheafification adjunct of `presheafComparison`. -/
theorem comparison_spec (φ : A ⟶ B) (i : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)
        ((comparison φ).f i) =
      (presheafComparison φ).f i :=
  sorry

/-- Unfolding of the components of `comparison`. -/
theorem comparison_f (φ : A ⟶ B) (i : ℤ) :
    (comparison φ).f i =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).symm
        ((presheafComparison φ).f i) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex.Sections
