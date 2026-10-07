module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Adjunction.Action
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Components

/-!
# Action of pointwise adjunctions on adjunction bicategories

This leaf completes the naturality cells of the action by their canonical
mates and assembles the resulting strong transformation. Mapping modifications
is in `PointwiseAdjunction.Action.Modification`.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

namespace PointwiseAdjunction

variable {η : F ⟶ G}

/-- The right-adjoint naturality isomorphism obtained as the mate of the original
left-adjoint naturality isomorphism. -/
def naturality.rightIso
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (h.app a.obj ≫ G.mapAdj.map f).r ≅
      (F.mapAdj.map f ≫ h.app b.obj).r :=
  Bicategory.conjugateIsoEquiv
    (h.app a.obj ≫ G.mapAdj.map f).adj
    (F.mapAdj.map f ≫ h.app b.obj).adj
    (η.naturality f.l)

/-- The forward morphism of the right-adjoint naturality isomorphism is the conjugate of
the original forward naturality cell. -/
@[simp]
theorem naturality.rightIso.hom
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (PointwiseAdjunction.naturality.rightIso h f).hom =
      Bicategory.conjugateEquiv
        (h.app a.obj ≫ G.mapAdj.map f).adj
        (F.mapAdj.map f ≫ h.app b.obj).adj
        (η.naturality f.l).hom := sorry

/-- The inverse morphism of the right-adjoint naturality isomorphism is the conjugate of
the original inverse naturality cell in the reverse direction. -/
@[simp]
theorem naturality.rightIso.inv
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (PointwiseAdjunction.naturality.rightIso h f).inv =
      Bicategory.conjugateEquiv
        (F.mapAdj.map f ≫ h.app b.obj).adj
        (h.app a.obj ≫ G.mapAdj.map f).adj
        (η.naturality f.l).inv := sorry

/-- The naturality isomorphism on adjunctions induced by a pointwise adjunction. Its left
component is the original naturality isomorphism and its right component is its mate. -/
@[stacks 0040 "naturality for the pointwise adjunction action"]
def naturality
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    F.mapAdj.map f ≫ h.app b.obj ≅
      h.app a.obj ≫ G.mapAdj.map f :=
  Bicategory.Adj.iso₂Mk
    (η.naturality f.l) (PointwiseAdjunction.naturality.rightIso h f)

/-- The forward left-adjoint component of induced `Adj`-naturality is the original forward
naturality cell. -/
@[simp]
theorem naturality.hom.τl
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (PointwiseAdjunction.naturality h f).hom.τl =
      (η.naturality f.l).hom := sorry

/-- The inverse left-adjoint component of induced `Adj`-naturality is the original inverse
naturality cell. -/
@[simp]
theorem naturality.inv.τl
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (PointwiseAdjunction.naturality h f).inv.τl =
      (η.naturality f.l).inv := sorry

/-- The forward right-adjoint component of induced `Adj`-naturality is the canonical mate. -/
@[simp]
theorem naturality.hom.τr
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (PointwiseAdjunction.naturality h f).hom.τr =
      (PointwiseAdjunction.naturality.rightIso h f).hom := sorry

/-- The inverse right-adjoint component of induced `Adj`-naturality is the inverse canonical
mate. -/
@[simp]
theorem naturality.inv.τr
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (PointwiseAdjunction.naturality h f).inv.τr =
      (PointwiseAdjunction.naturality.rightIso h f).inv := sorry

/-- Induced `Adj`-naturality is natural in mate `2`-morphisms of the source. -/
theorem naturality.map₂
    (h : PointwiseAdjunction η)
    {a b : Bicategory.Adj B} {f g : a ⟶ b} (γ : f ⟶ g) :
    F.mapAdj.map₂ γ ▷ h.app b.obj ≫
        (PointwiseAdjunction.naturality h g).hom =
      (PointwiseAdjunction.naturality h f).hom ≫
        h.app a.obj ◁ G.mapAdj.map₂ γ := sorry

/-- Induced `Adj`-naturality satisfies the identity coherence equation. -/
theorem naturality.id
    (h : PointwiseAdjunction η) (a : Bicategory.Adj B) :
    (PointwiseAdjunction.naturality h (𝟙 a)).hom ≫
        h.app a.obj ◁ (G.mapAdj.mapId a).hom =
      (F.mapAdj.mapId a).hom ▷ h.app a.obj ≫
        (λ_ (h.app a.obj)).hom ≫
        (ρ_ (h.app a.obj)).inv := sorry

/-- Induced `Adj`-naturality satisfies the composition coherence equation. -/
theorem naturality.comp
    (h : PointwiseAdjunction η)
    {a b c : Bicategory.Adj B} (f : a ⟶ b) (g : b ⟶ c) :
    (PointwiseAdjunction.naturality h (f ≫ g)).hom ≫
        h.app a.obj ◁ (G.mapAdj.mapComp f g).hom =
      (F.mapAdj.mapComp f g).hom ▷ h.app c.obj ≫
        (α_ _ _ _).hom ≫
        F.mapAdj.map f ◁ (PointwiseAdjunction.naturality h g).hom ≫
        (α_ _ _ _).inv ≫
        (PointwiseAdjunction.naturality h f).hom ▷ G.mapAdj.map g ≫
        (α_ _ _ _).hom := sorry

/-- A pointwise adjunction induces a strong transformation between the canonical actions on
bicategories of adjunctions. -/
@[stacks 0040 "action of a pointwise adjunction on adjunctions"]
def mapAdj (h : PointwiseAdjunction η) :
    StrongTrans F.mapAdj G.mapAdj where
  app a := h.app a.obj
  naturality f := PointwiseAdjunction.naturality h f
  naturality_naturality := PointwiseAdjunction.naturality.map₂ h
  naturality_id := PointwiseAdjunction.naturality.id h
  naturality_comp := PointwiseAdjunction.naturality.comp h

/-- The component of the induced strong transformation is the supplied pointwise
adjunction. -/
@[simp]
theorem mapAdj.app (h : PointwiseAdjunction η) (a : Bicategory.Adj B) :
    h.mapAdj.app a = h.app a.obj := sorry

/-- The left adjoint of an induced component is the original strong-transformation
component. -/
@[simp]
theorem mapAdj.app.l (h : PointwiseAdjunction η) (a : Bicategory.Adj B) :
    (h.mapAdj.app a).l = η.app a.obj := sorry

/-- The right adjoint of an induced component is the chosen pointwise right adjoint. -/
@[simp]
theorem mapAdj.app.r (h : PointwiseAdjunction η) (a : Bicategory.Adj B) :
    (h.mapAdj.app a).r = h.rightApp a.obj := sorry

/-- Naturality of the induced strong transformation is the mate-completed naturality
isomorphism. -/
@[simp]
theorem mapAdj.naturality
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    h.mapAdj.naturality f = PointwiseAdjunction.naturality h f := sorry

/-- The forward left-adjoint component of the induced strong-transformation naturality. -/
@[simp]
theorem mapAdj.naturality.hom.τl
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (h.mapAdj.naturality f).hom.τl =
      (η.naturality f.l).hom := sorry

/-- The inverse left-adjoint component of the induced strong-transformation naturality. -/
@[simp]
theorem mapAdj.naturality.inv.τl
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (h.mapAdj.naturality f).inv.τl =
      (η.naturality f.l).inv := sorry

/-- The forward right-adjoint component of the induced strong-transformation naturality. -/
@[simp]
theorem mapAdj.naturality.hom.τr
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (h.mapAdj.naturality f).hom.τr =
      (PointwiseAdjunction.naturality.rightIso h f).hom := sorry

/-- The inverse right-adjoint component of the induced strong-transformation naturality. -/
@[simp]
theorem mapAdj.naturality.inv.τr
    (h : PointwiseAdjunction η) {a b : Bicategory.Adj B}
    (f : a ⟶ b) :
    (h.mapAdj.naturality f).inv.τr =
      (PointwiseAdjunction.naturality.rightIso h f).inv := sorry

/- Data audit (mathlib 4.32): `naturality.rightIso` uses
`Bicategory.conjugateIsoEquiv`; the remaining deferred fields are mate
compatibility, naturality, and strong-transformation coherence. -/

end PointwiseAdjunction

end Pseudofunctor.StrongTrans

end CategoryTheory
