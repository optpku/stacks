/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.CategoryTheory.Inertia.Category
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia

For a functor `F : S ⥤ S'`, `RelativeInertia F` is the subcategory of `Inertia S`
whose chosen automorphism maps to the identity under `F`.
-/

open CategoryTheory

universe uC vC uS vS uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {S' : Type uS'} [Category.{vS'} S']

/- Axiom audit: `#print axioms` on `RelativeInertia.toInertiaFunctor`,
`RelativeInertia.identitySection.obj`, `RelativeInertia.identitySection.map`, and
`RelativeInertia.map` reports `sorryAx` only through Prop-valued intertwining, category, functor,
and kernel laws; no non-Prop witness is supplied by `sorry`. -/

/- `RelativeInertia F` is the full subcategory of `Inertia S` cut out by the kernel condition
`F.mapAut X.obj X.aut = 1`. The kernel subtype has named projections `.obj` and `.aut`,
while its category is induced from the generic inertia category below;
there is no second implementation of intertwiners or category laws.

The later `BasedCategory.PseudoPullback` constructions are semantic models in `Cat/C`, not the
definition of relative inertia. Source, target, and base categories therefore retain independent
object and morphism universes until those explicit pseudo-pullback specializations.

The defining square for a morphism is

```
             φ
  x ─────────────────▶ y
  │                     │
 α│                     │β
  ▼                     ▼
  x ─────────────────▶ y
             φ
```

with equation `α.hom ≫ φ = φ ≫ β.hom`. -/

/-- An object of the relative inertia of `F : S ⥤ S'` is an inertia object whose automorphism
maps to the neutral automorphism under `F`. -/
@[stacks 034I "abstract relative inertia category"]
def RelativeInertia (F : S ⥤ S') :=
  { X : Inertia S // F.mapAut X.obj X.aut = 1 }

/-- Construct a relative-inertia object from an inertia object satisfying the kernel condition. -/
def RelativeInertia.mk {F : S ⥤ S'} (toInertia : Inertia S)
    (mapAut_eq_one : F.mapAut toInertia.obj toInertia.aut = 1) : RelativeInertia F :=
  ⟨toInertia, mapAut_eq_one⟩

/-- The underlying inertia object. -/
abbrev RelativeInertia.toInertia {F : S ⥤ S'} (X : RelativeInertia F) : Inertia S := X.1

/-- The underlying object of relative inertia. -/
abbrev RelativeInertia.obj {F : S ⥤ S'} (X : RelativeInertia F) : S := X.toInertia.obj

/-- The chosen automorphism of a relative-inertia object. -/
abbrev RelativeInertia.aut {F : S ⥤ S'} (X : RelativeInertia F) : Aut X.obj :=
  X.toInertia.aut

/-- The chosen automorphism has neutral image. -/
theorem RelativeInertia.mapAut_eq_one {F : S ⥤ S'} (X : RelativeInertia F) :
    F.mapAut X.obj X.aut = 1 := X.2

attribute [stacks 034I "relative inertia underlying inertia field"] RelativeInertia.toInertia
attribute [stacks 034I "relative inertia kernel field"] RelativeInertia.mapAut_eq_one

/-- The hom-level consequence of the group-valued relative-inertia condition. This is the
bridge used by categorical constructions, which are stated in terms of ordinary morphisms. -/
@[simp, stacks 034I "relative-inertia kernel condition on morphisms"]
theorem RelativeInertia.mapAut_hom {F : S ⥤ S'} (X : RelativeInertia F) :
    F.map X.aut.hom = 𝟙 (F.obj X.obj) := sorry
/- Proof strategy: apply congruence to the `Iso.hom` projection of `X.mapAut_eq_one`, then unfold
`Functor.mapAut` and the neutral element of `Aut`. -/

variable (F : S ⥤ S')
section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The relative-inertia category is the full category induced from `Inertia S` by forgetting the
kernel proof. -/
instance RelativeInertia.category : Category (RelativeInertia F) :=
  inferInstanceAs
    (Category (InducedCategory (Inertia S) RelativeInertia.toInertia))

attribute [stacks 034I "relative inertia induced category"] RelativeInertia.category

/-- Build a relative-inertia morphism from an underlying arrow and its intertwining equation. -/
@[stacks 034I "construct a relative-inertia morphism"]
def RelativeInertia.homMk {X Y : RelativeInertia F} (f : X.obj ⟶ Y.obj)
    (naturality : X.aut.hom ≫ f = f ≫ Y.aut.hom) : X ⟶ Y :=
  InducedCategory.homMk (Inertia.homMk f naturality)

/-- The underlying arrow of a relative-inertia morphism. This transparent view hides only the
induced-category implementation layer. -/
@[stacks 034I "relative inertia underlying-arrow projection"]
abbrev RelativeInertia.hom {F : S ⥤ S'} {X Y : RelativeInertia F}
    (f : X ⟶ Y) : X.obj ⟶ Y.obj :=
  Inertia.hom f.hom

/-- The underlying arrow of a relative-inertia morphism intertwines the chosen automorphisms.

Proof strategy: project the generic `Inertia.hom.naturality` equation through the induced
category. -/
@[reassoc, stacks 034I "relative inertia intertwining readout"]
theorem RelativeInertia.hom.naturality {X Y : RelativeInertia F} (f : X ⟶ Y) :
    X.aut.hom ≫ RelativeInertia.hom f = RelativeInertia.hom f ≫ Y.aut.hom := sorry

/-- The underlying arrow of a relative-inertia morphism also intertwines the inverse
automorphisms. -/
@[reassoc, stacks 034I "relative inertia inverse intertwining readout"]
theorem RelativeInertia.hom.invNaturality {X Y : RelativeInertia F} (f : X ⟶ Y) :
    X.aut.inv ≫ RelativeInertia.hom f =
      RelativeInertia.hom f ≫ Y.aut.inv := sorry

/-- Relative-inertia morphisms are determined by their underlying arrows.

Proof strategy: apply `InducedCategory.hom_ext`, then `Inertia.hom_ext`. -/
@[ext, stacks 034I "relative inertia underlying-arrow extensionality"]
theorem RelativeInertia.hom_ext {X Y : RelativeInertia F} (f g : X ⟶ Y)
    (h : RelativeInertia.hom f = RelativeInertia.hom g) : f = g := sorry

/-- The underlying arrow of an identity relative-inertia morphism is an identity.

Proof strategy: use `Inertia.hom_id` through the induced category. -/
@[simp, stacks 034I "relative inertia identity underlying arrow"]
theorem RelativeInertia.hom_id (X : RelativeInertia F) :
    RelativeInertia.hom (𝟙 X) = 𝟙 X.obj := sorry

/-- The underlying arrow of a composite relative-inertia morphism is the composite of the
underlying arrows.

Proof strategy: use `Inertia.hom_comp` through the induced category. -/
@[simp, stacks 034I "relative inertia composition underlying arrow"]
theorem RelativeInertia.hom_comp {X Y Z : RelativeInertia F}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RelativeInertia.hom (f ≫ g) = RelativeInertia.hom f ≫ RelativeInertia.hom g := sorry

/-- A relative-inertia morphism is invertible when its underlying arrow is invertible.

Proof strategy: first lift invertibility to the generic inertia morphism, then use the fully
faithful induced-category structure. -/
@[stacks 034I "relative inertia invertibility from underlying arrow"]
theorem RelativeInertia.isIso_of_hom_isIso {X Y : RelativeInertia F} (f : X ⟶ Y)
    [IsIso (RelativeInertia.hom f)] : IsIso f := sorry

/-- Package an ambient isomorphism compatible with the chosen automorphisms as an isomorphism
of relative-inertia objects. The relative kernel proofs are inherited object properties and add
no new isomorphism data. -/
@[stacks 034I "construct a relative-inertia isomorphism"]
def RelativeInertia.isoMk {X Y : RelativeInertia F}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    X ≅ Y :=
  InducedCategory.isoMk (Inertia.isoMk e naturality)

/-- The underlying forward arrow of `RelativeInertia.isoMk` is the supplied ambient forward
arrow. -/
@[simp, stacks 034I "relative inertia isomorphism forward arrow"]
theorem RelativeInertia.isoMk.hom {X Y : RelativeInertia F}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    RelativeInertia.hom (RelativeInertia.isoMk F e naturality).hom =
      e.hom := sorry

/-- The underlying inverse arrow of `RelativeInertia.isoMk` is the supplied ambient inverse
arrow. -/
@[simp, stacks 034I "relative inertia isomorphism inverse arrow"]
theorem RelativeInertia.isoMk.inv {X Y : RelativeInertia F}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    RelativeInertia.hom (RelativeInertia.isoMk F e naturality).inv =
      e.inv := sorry

/-- Forget only the relative kernel condition, retaining the inertia object. -/
@[stacks 034I "relative inertia to absolute inertia"]
def RelativeInertia.toInertiaFunctor : RelativeInertia F ⥤ Inertia S :=
  inducedFunctor RelativeInertia.toInertia

/-- The induced inertia object is the parent field of a relative-inertia object.

Proof strategy: unfold `toInertiaFunctor`. -/
@[simp, stacks 034I "relative inertia to absolute inertia object"]
theorem RelativeInertia.toInertiaFunctor.obj (X : RelativeInertia F) :
    (RelativeInertia.toInertiaFunctor F).obj X = X.toInertia := sorry

/-- Forget the automorphism from a relative-inertia object. -/
@[stacks 042H "abstract relative-inertia forgetful functor"]
def RelativeInertia.forget : RelativeInertia F ⥤ S :=
  RelativeInertia.toInertiaFunctor F ⋙ Inertia.forget S

/-- Forgetting a relative-inertia object returns its underlying source object.

Proof strategy: unfold `forget` and `toInertiaFunctor`. -/
@[simp, stacks 042H "abstract relative-inertia forgetful object"]
theorem RelativeInertia.forget.obj (X : RelativeInertia F) :
    (RelativeInertia.forget F).obj X = X.obj := sorry

/-- Forgetting a relative-inertia morphism returns its underlying arrow.

Proof strategy: unfold `forget`, `toInertiaFunctor`, and `RelativeInertia.hom`. -/
@[simp, stacks 042H "abstract relative-inertia forgetful arrow"]
theorem RelativeInertia.forget.map {X Y : RelativeInertia F} (f : X ⟶ Y) :
    (RelativeInertia.forget F).map f = RelativeInertia.hom f := sorry

/-- Project relative inertia to any category receiving the source category. -/
@[stacks 034I "abstract relative-inertia projection"]
def RelativeInertia.projection (p : S ⥤ C) : RelativeInertia F ⥤ C :=
  RelativeInertia.forget F ⋙ p

/-- The relative-inertia projection maps objects through the chosen base functor.

Proof strategy: unfold `projection` and use `forget.obj`. -/
@[simp, stacks 034I "abstract relative-inertia projection on objects"]
theorem RelativeInertia.projection.obj (p : S ⥤ C) (X : RelativeInertia F) :
    (RelativeInertia.projection F p).obj X = p.obj X.obj := sorry

/-- The relative-inertia projection maps underlying arrows through the chosen base functor.

Proof strategy: unfold `projection` and use `forget.map`. -/
@[simp, stacks 034I "abstract relative-inertia projection on arrows"]
theorem RelativeInertia.projection.map (p : S ⥤ C) {X Y : RelativeInertia F} (f : X ⟶ Y) :
    (RelativeInertia.projection F p).map f = p.map (RelativeInertia.hom f) := sorry

/-- Identity automorphisms satisfy the relative-inertia object condition. -/
private theorem RelativeInertia.identitySection.impl.mapAut_eq_one (X : S) :
    F.mapAut X (1 : Aut X) = 1 := sorry
/- Proof strategy: use the monoid-homomorphism law `map_one`. -/

/-- The relative neutral object is the generic inertia identity-section object equipped with the
kernel proof. -/
@[stacks 04Z3 "relative inertia neutral object"]
def RelativeInertia.identitySection.obj (X : S) : RelativeInertia F :=
  RelativeInertia.mk ((Inertia.identitySection S).obj X)
    (RelativeInertia.identitySection.impl.mapAut_eq_one F X)

/-- The relative neutral-section morphism is the generic inertia identity-section morphism,
viewed in the induced subcategory. -/
@[stacks 04Z3 "relative inertia neutral arrow"]
def RelativeInertia.identitySection.map {X Y : S} (f : X ⟶ Y) :
    RelativeInertia.identitySection.obj F X ⟶ RelativeInertia.identitySection.obj F Y :=
  InducedCategory.homMk ((Inertia.identitySection S).map f)

/-- The neutral-section map preserves identities. -/
private theorem RelativeInertia.identitySection.impl.map_id (X : S) :
    RelativeInertia.identitySection.map F (𝟙 X) =
      𝟙 (RelativeInertia.identitySection.obj F X) := sorry
/- Proof strategy: apply `RelativeInertia.hom_ext`; both underlying arrows are identities. -/

/-- The neutral-section map preserves composition. -/
private theorem RelativeInertia.identitySection.impl.map_comp
    {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    RelativeInertia.identitySection.map F (f ≫ g) =
      RelativeInertia.identitySection.map F f ≫
        RelativeInertia.identitySection.map F g := sorry
/- Proof strategy: apply `RelativeInertia.hom_ext`; the underlying arrows agree definitionally. -/

/-- The neutral section of relative inertia, selecting the identity automorphism at every object. -/
@[stacks 04Z3 "abstract relative-inertia neutral section"]
def RelativeInertia.identitySection : S ⥤ RelativeInertia F where
  obj := RelativeInertia.identitySection.obj F
  map := RelativeInertia.identitySection.map F
  map_id := RelativeInertia.identitySection.impl.map_id F
  map_comp := RelativeInertia.identitySection.impl.map_comp F

/-- The neutral section is a right inverse to the relative-inertia structure functor. -/
@[simp, stacks 04Z3 "abstract relative-inertia identity-section round trip"]
theorem RelativeInertia.identitySection.comp_forget :
    RelativeInertia.identitySection F ⋙ RelativeInertia.forget F = 𝟭 S := sorry
/- Proof strategy: apply functor extensionality; both object and morphism maps are identities. -/

/-- The neutral section selects the identity automorphism. -/
@[simp, stacks 04Z3 "abstract relative-inertia identity automorphism"]
theorem RelativeInertia.identitySection.obj.aut (X : S) :
    ((RelativeInertia.identitySection F).obj X).aut = 1 := sorry
/- Proof strategy: unfold `RelativeInertia.identitySection`. -/

/-- The relative neutral section retains the underlying object. -/
@[simp, stacks 04Z3 "abstract relative-inertia identity-section object"]
theorem RelativeInertia.identitySection.obj.underlying (X : S) :
    ((RelativeInertia.identitySection F).obj X).obj = X := sorry

/-- The relative neutral section retains the underlying arrow. -/
@[simp, stacks 04Z3 "abstract relative-inertia identity-section arrow"]
theorem RelativeInertia.identitySection.map.hom {X Y : S} (f : X ⟶ Y) :
    RelativeInertia.hom ((RelativeInertia.identitySection F).map f) = f := sorry

namespace RelativeInertia.forget

/-- If the defining functor is faithful, forgetting a relative-inertia automorphism is an
equivalence: the kernel condition forces that automorphism to be the identity. -/
instance isEquivalenceOfFaithful [F.Faithful] :
    (RelativeInertia.forget F).IsEquivalence := sorry
/- Proof strategy: use `RelativeInertia.identitySection F` as a quasi-inverse. Faithfulness of
`F` identifies every selected kernel automorphism with the identity, giving the remaining
objectwise isomorphism. -/

end RelativeInertia.forget

/-- Mapping an inertia automorphism through an invertible comparison square preserves the
neutral-image condition. -/
private theorem RelativeInertia.Map.obj_mapAut_eq_one
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) (X : RelativeInertia F₁) :
    F₂.mapAut (G.obj X.obj) (G.mapIso X.aut) = 1 := sorry
/- Proof strategy: apply `Aut.ext`, use naturality of `τ` on `X.aut.hom`, and finish with the
hom-level bridge `X.mapAut_hom`. -/

/-- Object map induced on relative inertia by an invertibly commuting functor square. Its inertia
datum is supplied by the generic `Inertia.map`; only preservation of the kernel condition is new. -/
private def RelativeInertia.Map.obj
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) (X : RelativeInertia F₁) : RelativeInertia F₂ :=
  RelativeInertia.mk ((Inertia.map G).obj X.toInertia)
    (RelativeInertia.Map.obj_mapAut_eq_one G G' τ X)

/-- Morphism map induced on relative inertia by an invertibly commuting functor square. It is the
generic inertia map viewed in the induced subcategory. -/
private def RelativeInertia.Map.map
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) {X Y : RelativeInertia F₁} (f : X ⟶ Y) :
    RelativeInertia.Map.obj G G' τ X ⟶ RelativeInertia.Map.obj G G' τ Y :=
  InducedCategory.homMk ((Inertia.map G).map f.hom)

/-- The induced map on relative inertia preserves identities. -/
private theorem RelativeInertia.Map.map_id
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) (X : RelativeInertia F₁) :
    RelativeInertia.Map.map G G' τ (𝟙 X) = 𝟙 (RelativeInertia.Map.obj G G' τ X) := sorry
/- Proof strategy: apply `RelativeInertia.hom_ext` and use `G.map_id`. -/

/-- The induced map on relative inertia preserves composition. -/
private theorem RelativeInertia.Map.map_comp
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) {X Y Z : RelativeInertia F₁}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RelativeInertia.Map.map G G' τ (f ≫ g) =
      RelativeInertia.Map.map G G' τ f ≫ RelativeInertia.Map.map G G' τ g := sorry
/- Proof strategy: apply `RelativeInertia.hom_ext` and use `G.map_comp`. -/

/-- An invertibly commuting square induces a functor on relative inertia. -/
@[stacks 04Z4 "abstract relative-inertia functoriality"]
def RelativeInertia.map
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) : RelativeInertia F₁ ⥤ RelativeInertia F₂ where
  obj := RelativeInertia.Map.obj G G' τ
  map := RelativeInertia.Map.map G G' τ
  map_id := RelativeInertia.Map.map_id G G' τ
  map_comp := RelativeInertia.Map.map_comp G G' τ

end

/-- The induced inertia functor maps the underlying object by `G`. -/
@[simp, stacks 04Z4 "abstract relative-inertia square map on objects"]
theorem RelativeInertia.map.obj.underlying
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) (X : RelativeInertia F₁) :
    ((RelativeInertia.map G G' τ).obj X).obj = G.obj X.obj := sorry
/- Proof strategy: unfold the object component of `RelativeInertia.map`. -/

/-- The induced inertia functor maps the chosen automorphism by `G.mapIso`. -/
@[simp, stacks 04Z4 "abstract relative-inertia square map on automorphisms"]
theorem RelativeInertia.map.obj.aut
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) (X : RelativeInertia F₁) :
    ((RelativeInertia.map G G' τ).obj X).aut = G.mapIso X.aut := sorry
/- Proof strategy: unfold the object component of `RelativeInertia.map`. -/

/-- The induced inertia functor maps an underlying arrow by `G.map`. -/
@[simp, stacks 04Z4 "abstract relative-inertia square map on arrows"]
theorem RelativeInertia.map.hom
    {S₁ S₁' S₂ S₂' : Type*}
    [Category S₁] [Category S₁'] [Category S₂] [Category S₂']
    {F₁ : S₁ ⥤ S₁'} {F₂ : S₂ ⥤ S₂'} (G : S₁ ⥤ S₂) (G' : S₁' ⥤ S₂')
    (τ : F₁ ⋙ G' ≅ G ⋙ F₂) {X Y : RelativeInertia F₁} (f : X ⟶ Y) :
    RelativeInertia.hom ((RelativeInertia.map G G' τ).map f) =
      G.map (RelativeInertia.hom f) := sorry
/- Proof strategy: unfold the morphism component of `RelativeInertia.map`. -/

variable (p : S ⥤ C)
variable {p}
variable (p' : S' ⥤ C)

/-- A relative-inertia automorphism is vertical over the common base. -/
theorem RelativeInertia.base_eq_id (comm : F ⋙ p' = p)
    (X : RelativeInertia F) : p.map X.aut.hom = 𝟙 (p.obj X.obj) := sorry
/- Proof strategy: apply `p'.map` to `X.mapAut_hom` and transport across `comm`. -/

end CategoryTheory
