module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.RingTheory.Kaehler.DeRham.Map
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# De Rham complexes of commutative-ring presheaves

For a morphism `φ : O₁ ⟶ O₂` of commutative-ring presheaves, relative `p`-forms form a
presheaf of `O₂`-modules.  Restriction of scalars along `φ` gives the `O₁`-module presheaf which is
the degree-`p` term of the de Rham complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u v

namespace PresheafOfModules.DeRham

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- Naturality of a ring-presheaf morphism, packaged as the square used by de Rham
functoriality. -/
theorem square (φ : O₁ ⟶ O₂) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    CommSq (O₁.map f) (φ.app X) (φ.app Y) (O₂.map f) := sorry

/-- The identity law required by the presheaf of relative differential forms. -/
theorem formMapId (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ) :
    CommRingCat.DeRham.formMapApp (square φ (𝟙 X)) p =
      (ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app _ := sorry

/-- The composition law required by the presheaf of relative differential forms. -/
theorem formMapComp (φ : O₁ ⟶ O₂) (p : ℕ)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CommRingCat.DeRham.formMapApp (square φ (f ≫ g)) p =
      CommRingCat.DeRham.formMapApp (square φ f) p ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₂).map f).hom)).map
          (CommRingCat.DeRham.formMapApp (square φ g) p) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringPresheaf O₂).map f).hom) (((ringPresheaf O₂).map g).hom)
          (((ringPresheaf O₂).map (f ≫ g)).hom)
          (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_comp f g))).inv.app _ := sorry

/-- The presheaf of relative differential `p`-forms, retaining its natural `O₂`-module
structure. -/
@[stacks 0FKM]
noncomputable def form (φ : O₁ ⟶ O₂) (p : ℕ) :
    PresheafOfModules.{max u v} (ringPresheaf O₂) where
  obj X := CommRingCat.DeRham.form (φ.app X) p
  map f := CommRingCat.DeRham.formMapApp (square φ f) p
  map_id X := formMapId φ p X
  map_comp f g := formMapComp φ p f g

/-- Restriction from `O₂`-module presheaves to `O₁`-module presheaves along `φ`. -/
@[stacks 0FKM "restriction along a morphism of commutative-ring presheaves"]
abbrev restriction (φ : O₁ ⟶ O₂) :=
  PresheafOfModules.restrictScalars (presheafStructureMap φ)

/-- The scalar-restricted degree-`p` term of the presheaf de Rham complex. -/
@[stacks 0FKM]
noncomputable def term (φ : O₁ ⟶ O₂) (p : ℕ) :
    PresheafOfModules.{max u v} (ringPresheaf O₁) :=
  (restriction φ).obj (form φ p)

/-- The value of the form presheaf is the algebraic form module of the section-ring map. -/
theorem form_obj (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ) :
    (form φ p).obj X = CommRingCat.DeRham.form (φ.app X) p := sorry

/-- Restriction of relative forms is induced by the naturality square of the ring map. -/
theorem form_map (φ : O₁ ⟶ O₂) (p : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (form φ p).map f = CommRingCat.DeRham.formMapApp (square φ f) p := sorry

/-- The value of a scalar-restricted term is the scalar-restricted algebraic form module. -/
theorem term_obj (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ) :
    (term φ p).obj X = CommRingCat.DeRham.term (φ.app X) p := sorry

/-- A basic relative form in the target-ring module presheaf. -/
def basic (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ)
    (b₀ : O₂.obj X) (bs : Fin p → O₂.obj X) : (form φ p).obj X :=
  CommRingCat.DeRham.basic (φ.app X) p b₀ bs

/-- A basic relative form viewed in the scalar-restricted de Rham term. -/
def termBasic (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ)
    (b₀ : O₂.obj X) (bs : Fin p → O₂.obj X) : (term φ p).obj X :=
  CommRingCat.DeRham.basic (φ.app X) p b₀ bs

/-- The sectionwise de Rham differentials are natural with respect to restriction. -/
theorem d_naturality (φ : O₁ ⟶ O₂) (p : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (term φ p).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₁).map f).hom)).map
          (CommRingCat.DeRham.d (φ.app Y) p) =
      CommRingCat.DeRham.d (φ.app X) p ≫ (term φ (p + 1)).map f := sorry

/-- The degree-raising differential between scalar-restricted presheaves of forms. -/
@[stacks 0FKM]
noncomputable def d (φ : O₁ ⟶ O₂) (p : ℕ) : term φ p ⟶ term φ (p + 1) where
  app X := CommRingCat.DeRham.d (φ.app X) p
  naturality f := d_naturality φ p f

/-- Equation 17.30.1.1 (0FKN): the differential satisfies the basic-form formula objectwise. -/
@[stacks 0FKN]
theorem d_basic (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ)
    (b₀ : O₂.obj X) (bs : Fin p → O₂.obj X) :
    (d φ p).app X (termBasic φ p X b₀ bs) =
      termBasic φ (p + 1) X 1 (Fin.cons b₀ bs) := sorry

/-- Consecutive presheaf de Rham differentials compose to zero. -/
@[stacks 0FKM "differential squares to zero"]
theorem d_sq (φ : O₁ ⟶ O₂) (p : ℕ) :
    d φ p ≫ d φ (p + 1) = 0 := sorry

/-- The de Rham complex of a morphism of commutative-ring presheaves. -/
@[stacks 0FKM]
noncomputable def complex (φ : O₁ ⟶ O₂) :
    CochainComplex (PresheafOfModules.{max u v} (ringPresheaf O₁)) ℕ :=
  CochainComplex.of (term φ) (d φ) (d_sq φ)

/-- The degree-`p` object of the presheaf de Rham complex is `term φ p`. -/
@[stacks 0FKM "term component"]
theorem complex_X (φ : O₁ ⟶ O₂) (p : ℕ) :
    (complex φ).X p = term φ p := sorry

/-- The consecutive-degree map of the presheaf de Rham complex is `d φ p`. -/
@[stacks 0FKM "differential component"]
theorem complex_d (φ : O₁ ⟶ O₂) (p : ℕ) :
    (complex φ).d p (p + 1) = d φ p := sorry

end PresheafOfModules.DeRham
