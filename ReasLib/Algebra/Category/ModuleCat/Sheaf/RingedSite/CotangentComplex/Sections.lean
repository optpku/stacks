module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Homology
public import Mathlib.Algebra.Homology.Additive

/-!
# Objectwise sections of the ring-sheaf cotangent complex

The rule `U ↦ L(B(U)/A(U))` forms a cochain complex of `B`-module presheaves.
Its sheafification has a canonical comparison to the sheaf cotangent complex.
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
    ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (CotangentComplex.obj A (Under.mk φ)) ⟶
      ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.evaluation.{u} (ringSheaf J B) Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (CotangentComplex.obj A (Under.mk φ))) where
  f i := ((CotangentComplex.obj A (Under.mk φ)).X i).val.map f
  comm' := sorry

private theorem complex_map_id (φ : A ⟶ B) (i : ℤ) (X : Cᵒᵖ) :
    (Homology.complexMap φ (𝟙 X)).f i =
      (ModuleCat.restrictScalarsId' ((ringSheaf J B).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((ringSheaf J B).obj.map_id X))).inv.app
          ((RingHom.cotangentComplex (φ.hom.app X).hom).X i) :=
  sorry

private theorem complex_map_comp (φ : A ⟶ B) (i : ℤ) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Homology.complexMap φ (f ≫ g)).f i =
      (Homology.complexMap φ f).f i ≫
        (ModuleCat.restrictScalars ((ringSheaf J B).obj.map f).hom).map
          ((Homology.complexMap φ g).f i) ≫
        (ModuleCat.restrictScalarsComp' ((ringSheaf J B).obj.map f).hom
          ((ringSheaf J B).obj.map g).hom ((ringSheaf J B).obj.map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((ringSheaf J B).obj.map_comp f g))).inv.app
            ((RingHom.cotangentComplex (φ.hom.app Z).hom).X i) :=
  sorry

private theorem complex_d_naturality (φ : A ⟶ B) (i j : ℤ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) :
    (Homology.complexMap φ f).f i ≫
        (ModuleCat.restrictScalars ((ringSheaf J B).obj.map f).hom).map
          ((RingHom.cotangentComplex (φ.hom.app Y).hom).d i j) =
      (RingHom.cotangentComplex (φ.hom.app X).hom).d i j ≫
        (Homology.complexMap φ f).f j :=
  sorry

private theorem complex_shape (φ : A ⟶ B) (i j : ℤ)
    (h : ¬ (ComplexShape.up ℤ).Rel i j) (U : Cᵒᵖ) :
    (RingHom.cotangentComplex (φ.hom.app U).hom).d i j = 0 :=
  sorry

/-- The cochain complex of `B`-module presheaves with value `U ↦ L(B(U)/A(U))`. -/
def complex (φ : A ⟶ B) :
    CochainComplex (PresheafOfModules (ringSheaf J B).obj) ℤ where
  X i :=
    { obj U := (RingHom.cotangentComplex (φ.hom.app U).hom).X i
      map f := (Homology.complexMap φ f).f i
      map_id X := by exact complex_map_id φ i X
      map_comp f g := by exact complex_map_comp φ i f g }
  d i j :=
    { app U := (RingHom.cotangentComplex (φ.hom.app U).hom).d i j
      naturality f := by exact complex_d_naturality φ i j f }
  shape i j h := by
    ext1 U
    exact complex_shape φ i j h U
  d_comp_d' := sorry

/-- The terms of the presheaf complex are the terms of the section-ring cotangent complexes. -/
theorem complex_X (φ : A ⟶ B) (i : ℤ) (U : Cᵒᵖ) :
    ((complex φ).X i).obj U = (RingHom.cotangentComplex (φ.hom.app U).hom).X i :=
  rfl

/-- The canonical section maps of cotangent complexes commute with restriction. -/
theorem sectionsComplexMap_naturality (φ : A ⟶ B) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Homology.sectionsComplexMap φ X ≫ evalRestrict φ f =
      Homology.complexMap φ f ≫
        ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (Homology.sectionsComplexMap φ Y) :=
  sorry

/-- The canonical section maps assemble into a morphism from the objectwise cotangent
complex to the underlying presheaf complex of the sheaf cotangent complex. -/
def presheafComparison (φ : A ⟶ B) :
    complex φ ⟶
      ((PresheafOfModules.restrictScalars (𝟙 (ringSheaf J B).obj)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.forget (ringSheaf J B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (CotangentComplex.obj A (Under.mk φ))) where
  f i :=
    { app U := (Homology.sectionsComplexMap φ U).f i
      naturality f := by
        ext x
        exact (CategoryTheory.congr_fun
          (congrArg (fun k => k.f i) (sectionsComplexMap_naturality φ f)) x).symm }
  comm' := sorry

/-- The components of the presheaf comparison are the canonical section maps. -/
theorem presheafComparison_f_app (φ : A ⟶ B) (i : ℤ) (U : Cᵒᵖ) :
    ((presheafComparison φ).f i).app U = (Homology.sectionsComplexMap φ U).f i :=
  rfl

private theorem sheafify_shape (φ : A ⟶ B) (i j : ℤ)
    (h : ¬ (ComplexShape.up ℤ).Rel i j) :
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).map
        ((complex φ).d i j) = 0 :=
  sorry

/-- The degreewise sheafification of the objectwise section-ring cotangent complex. -/
def sheafify (φ : A ⟶ B) :
    CochainComplex (SheafOfModules (ringSheaf J B)) ℤ where
  X i :=
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj ((complex φ).X i)
  d i j :=
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).map ((complex φ).d i j)
  shape i j h := by exact sheafify_shape φ i j h
  d_comp_d' := sorry

/-- Each term of the sheafified complex is the associated sheaf of the corresponding
term of the objectwise complex. -/
theorem sheafify_X (φ : A ⟶ B) (i : ℤ) :
    (sheafify φ).X i =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J B).obj)).obj ((complex φ).X i) :=
  rfl

/-- The canonical comparison from the sheafified objectwise cotangent complex to the
sheaf cotangent complex. -/
def comparison (φ : A ⟶ B) : sheafify φ ⟶ CotangentComplex.obj A (Under.mk φ) where
  f i :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).symm
      ((presheafComparison φ).f i)
  comm' := sorry

/-- The comparison morphism is the sheafification adjunct of the presheaf comparison. -/
theorem comparison_spec (φ : A ⟶ B) (i : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)
        ((comparison φ).f i) =
      (presheafComparison φ).f i :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).apply_symm_apply
    ((presheafComparison φ).f i)

/-- Each component of the comparison is the adjunct of the corresponding component
of the presheaf comparison. -/
theorem comparison_f (φ : A ⟶ B) (i : ℤ) :
    (comparison φ).f i =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J B).obj)).symm
        ((presheafComparison φ).f i) :=
  rfl

/-- The canonical comparison from the sheafified objectwise cotangent complex to the
sheaf cotangent complex is an isomorphism. -/
instance comparison_isIso (φ : A ⟶ B) : IsIso (comparison φ) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex.Sections
