/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction

/-!
# Basic strict costructured arrows

The generic owner for strict costructured-arrow objects, maps, and cells.  Its
computational API for identities, composites, and whiskering is in
`StrictCostructuredArrow.Computations`; `StrictSlice` is the specialization to
the identity strict pseudofunctor.
-/

@[expose] public section

universe wA vA uA wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- An object of the strict costructured-arrow bicategory of `K` over `X`: an object `left : A`
together with a structural `1`-morphism `K.obj left ⟶ X`. -/
@[ext]
structure StrictCostructuredArrow (K : StrictPseudofunctor A C) (X : C) where
  /-- The source object of the structural arrow. -/
  left : A
  /-- The structural arrow to the fixed target. -/
  hom : K.obj left ⟶ X

namespace StrictCostructuredArrow

variable [Bicategory.Strict A] [Bicategory.Strict C]
variable {K : StrictPseudofunctor A C} {X : C}

namespace Implementation

/-- Regard a strict costructured-arrow object as a colax costructured arrow with the same
non-Prop data. -/
def toColax (S : StrictCostructuredArrow K X) :
    ColaxCostructuredArrow K.toPseudofunctor X :=
  ColaxCostructuredArrow.mk S.left S.hom

/-- The hom property selecting colax morphisms whose normalized comparison cell is induced by an
actual equality of structural arrows. -/
def strictHomProperty (K : StrictPseudofunctor A C) (X : C) :
    HomProperty (fun S : StrictCostructuredArrow K X ↦ toColax S) :=
  fun S T f ↦
    ∃ h : K.map (ColaxCostructuredArrow.map f) ≫ T.hom = S.hom,
      ColaxCostructuredArrow.fac f = eqToHom h

/-- Identity colax morphisms satisfy the strict comparison property. -/
theorem strictHomProperty.id_mem (K : StrictPseudofunctor A C) (X : C)
    (S : StrictCostructuredArrow K X) :
    strictHomProperty K X S S (𝟙 (toColax S)) := sorry

/-- The strict comparison property is closed under composition. -/
theorem strictHomProperty.comp_mem (K : StrictPseudofunctor A C) (X : C)
    {S T U : StrictCostructuredArrow K X}
    {f : toColax S ⟶ toColax T} {g : toColax T ⟶ toColax U}
    (hf : strictHomProperty K X S T f)
    (hg : strictHomProperty K X T U g) :
    strictHomProperty K X S U (f ≫ g) := sorry

/-- The strict comparison property is multiplicative. -/
instance strictHomProperty.isMultiplicative (K : StrictPseudofunctor A C) (X : C) :
    (strictHomProperty K X).IsMultiplicative where
  id_mem := strictHomProperty.id_mem K X
  comp_mem := strictHomProperty.comp_mem K X

end Implementation

/-- The bicategory of strict costructured arrows, obtained as the locally induced part of the
colax costructured-arrow bicategory whose comparison cells come from equalities. -/
instance bicategory : Bicategory (StrictCostructuredArrow K X) :=
  inferInstanceAs
    (Bicategory
      (LocallyInducedBicategory
        (ColaxCostructuredArrow K.toPseudofunctor X)
        (fun S : StrictCostructuredArrow K X ↦ Implementation.toColax S)
        (Implementation.strictHomProperty K X)))

/-- Left composition by the identity is strictly unital for strict costructured arrows. -/
theorem strict_id_comp {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    𝟙 S ≫ f = f := sorry

/-- Right composition by the identity is strictly unital for strict costructured arrows. -/
theorem strict_comp_id {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    f ≫ 𝟙 T = f := sorry

/-- Composition of strict costructured-arrow morphisms is strictly associative. -/
theorem strict_assoc {R S T U : StrictCostructuredArrow K X}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := sorry

/-- The left unitor of a strict costructured-arrow morphism is induced by strict unitality. -/
theorem strict_leftUnitor_eqToIso {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    λ_ f = eqToIso (strict_id_comp f) := sorry

/-- The right unitor of a strict costructured-arrow morphism is induced by strict unitality. -/
theorem strict_rightUnitor_eqToIso {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    ρ_ f = eqToIso (strict_comp_id f) := sorry

/-- The associator of strict costructured-arrow morphisms is induced by strict associativity. -/
theorem strict_associator_eqToIso {R S T U : StrictCostructuredArrow K X}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    α_ f g h = eqToIso (strict_assoc f g h) := sorry

/-- The strict costructured-arrow bicategory is strict. -/
instance strict : Bicategory.Strict (StrictCostructuredArrow K X) where
  id_comp := strict_id_comp
  comp_id := strict_comp_id
  assoc := strict_assoc
  leftUnitor_eqToIso := strict_leftUnitor_eqToIso
  rightUnitor_eqToIso := strict_rightUnitor_eqToIso
  associator_eqToIso := strict_associator_eqToIso

/-- The source map underlying a strict costructured-arrow `1`-morphism. -/
def map {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    S.left ⟶ T.left :=
  ColaxCostructuredArrow.map f.obj

/-- The source map of a strict costructured-arrow morphism makes its structural triangle commute
strictly. -/
theorem comm {S T : StrictCostructuredArrow K X} (f : S ⟶ T) :
    K.map (map f) ≫ T.hom = S.hom := sorry

namespace Implementation

/-- The colax morphism built from a strictly commuting source map belongs to the strict hom
property. -/
theorem homMk_mem {S T : StrictCostructuredArrow K X}
    (map : S.left ⟶ T.left) (comm : K.map map ≫ T.hom = S.hom) :
    strictHomProperty K X S T
      (ColaxCostructuredArrow.homMk map (eqToHom comm)) := sorry

end Implementation

/-- Construct a strict costructured-arrow `1`-morphism from a source map and a strictly commuting
triangle. -/
def homMk {S T : StrictCostructuredArrow K X}
    (map : S.left ⟶ T.left) (comm : K.map map ≫ T.hom = S.hom) :
    S ⟶ T :=
  LocallyInducedBicategory.mkHom
    (ColaxCostructuredArrow.homMk map (eqToHom comm))
    (Implementation.homMk_mem map comm)

/-- The source map of a constructed strict costructured-arrow morphism is the supplied map. -/
@[simp]
theorem homMk_map {S T : StrictCostructuredArrow K X}
    (map : S.left ⟶ T.left) (comm : K.map map ≫ T.hom = S.hom) :
    StrictCostructuredArrow.map (homMk map comm) = map := sorry

/-- Strict costructured-arrow morphisms are determined by their source maps. -/
@[ext]
theorem hom_ext {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    (h : map f = map g) : f = g := sorry

/-- The source `2`-morphism underlying a strict costructured-arrow `2`-morphism. -/
def map₂ {S T : StrictCostructuredArrow K X} {f g : S ⟶ T} (η : f ⟶ g) :
    map f ⟶ map g :=
  ColaxCostructuredArrow.map₂ η.hom

/-- A source `2`-morphism underlying a strict costructured-arrow `2`-morphism is compatible with
the two strict comparison equalities. -/
theorem map₂_comm {S T : StrictCostructuredArrow K X} {f g : S ⟶ T} (η : f ⟶ g) :
    K.map₂ (map₂ η) ▷ T.hom ≫ eqToHom (comm g) =
      eqToHom (comm f) := sorry

namespace Implementation

/-- Convert strict `2`-cell compatibility into the normalized colax compatibility equation. -/
theorem hom₂Mk_w {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : K.map₂ η ▷ T.hom ≫ eqToHom (StrictCostructuredArrow.comm g) =
      eqToHom (StrictCostructuredArrow.comm f)) :
    ((Implementation.toColax T).comparison S.left).map η ≫
        ColaxCostructuredArrow.fac g.obj =
      ColaxCostructuredArrow.fac f.obj := sorry

/-- The ambient colax `2`-morphism determined by a compatible source cell. -/
def rawHom₂Mk {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : K.map₂ η ▷ T.hom ≫ eqToHom (StrictCostructuredArrow.comm g) =
      eqToHom (StrictCostructuredArrow.comm f)) :
    f.obj ⟶ g.obj :=
  ColaxCostructuredArrow.hom₂Mk η (hom₂Mk_w η comm)

end Implementation

/-- Construct a strict costructured-arrow `2`-morphism from a source cell satisfying the strict
compatibility equation. -/
def hom₂Mk {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : K.map₂ η ▷ T.hom ≫ eqToHom (StrictCostructuredArrow.comm g) =
      eqToHom (StrictCostructuredArrow.comm f)) :
    f ⟶ g :=
  ObjectProperty.homMk (Implementation.rawHom₂Mk η comm)

/-- The source cell of a constructed strict costructured-arrow `2`-morphism is the supplied cell. -/
@[simp]
theorem hom₂Mk_map₂ {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    (η : map f ⟶ map g)
    (comm : K.map₂ η ▷ T.hom ≫ eqToHom (StrictCostructuredArrow.comm g) =
      eqToHom (StrictCostructuredArrow.comm f)) :
    map₂ (hom₂Mk η comm) = η := sorry

/-- Strict costructured-arrow `2`-morphisms are determined by their source cells. -/
@[ext]
theorem hom₂_ext {S T : StrictCostructuredArrow K X} {f g : S ⟶ T}
    {η θ : f ⟶ g} (h : map₂ η = map₂ θ) :
    η = θ := sorry

end StrictCostructuredArrow

end Bicategory

end CategoryTheory
