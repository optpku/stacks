/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Inertia categories

This module defines the category of objects equipped with an automorphism and arrows
intertwining those automorphisms.  It is independent of any fibred-category presentation.
-/

open CategoryTheory

universe uC vC uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

/- Mathlib 4.32 provides the automorphism group `Aut X`, but not the category whose objects are
automorphisms and whose arrows intertwine them. That category is the reusable owner below. For a
groupoid it is the usual inertia (or free-loop) groupoid. Encoding it as a functor category out of
the delooping of `ℤ` is semantically equivalent, but would replace the two source-facing fields by
a heavier dependent functor; the explicit owner is the useful formal interface. -/

/-- The inertia category of `C` has objects `(X, α)` with `α : Aut X`. -/
@[stacks 034I "abstract inertia category"]
def Inertia (C : Type uC) [Category.{vC} C] := Σ X : C, Aut X

/-- Construct an inertia object from its object and automorphism. -/
def Inertia.mk (obj : C) (aut : Aut obj) : Inertia C := ⟨obj, aut⟩

/-- The underlying object of an inertia object. -/
abbrev Inertia.obj (X : Inertia C) : C := X.1

/-- The chosen automorphism of an inertia object. -/
abbrev Inertia.aut (X : Inertia C) : Aut X.obj := X.2

attribute [stacks 034I "inertia underlying object field"] Inertia.obj
attribute [stacks 034I "inertia automorphism field"] Inertia.aut

namespace Inertia

variable {D : Type uS'} [Category.{vS'} D]

/-- A morphism in `Inertia C` is an arrow intertwining the chosen automorphisms. -/
@[stacks 034I "abstract inertia morphism"]
def Hom (X Y : Inertia C) :=
  { f : X.obj ⟶ Y.obj // X.aut.hom ≫ f = f ≫ Y.aut.hom }

/-- Construct an intertwiner from an arrow and its equation. -/
def Hom.mk {X Y : Inertia C} (hom : X.obj ⟶ Y.obj)
    (naturality : X.aut.hom ≫ hom = hom ≫ Y.aut.hom) : Hom X Y :=
  ⟨hom, naturality⟩

/-- The underlying arrow of an intertwiner. -/
abbrev Hom.hom {X Y : Inertia C} (f : Hom X Y) : X.obj ⟶ Y.obj := f.1

/-- The defining intertwining equation. -/
theorem Hom.naturality {X Y : Inertia C} (f : Hom X Y) :
    X.aut.hom ≫ f.hom = f.hom ≫ Y.aut.hom := f.2

/-- Intertwiners are determined by their underlying arrows. -/
theorem Hom.ext {X Y : Inertia C} {f g : Hom X Y} (h : f.hom = g.hom) : f = g :=
  Subtype.ext h

attribute [stacks 034I "inertia underlying arrow field"] Inertia.Hom.hom
attribute [stacks 034I "inertia intertwining field"] Inertia.Hom.naturality

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Identity arrows intertwine every automorphism.

Proof strategy: simplify both unit composites. -/
private theorem idHom_naturality (X : Inertia C) :
    X.aut.hom ≫ 𝟙 X.obj = 𝟙 X.obj ≫ X.aut.hom := sorry

/-- Composition preserves the intertwining equation.

Proof strategy: reassociate and rewrite with the two input equations. -/
private theorem compHom_naturality {X Y Z : Inertia C} (f : Hom X Y) (g : Hom Y Z) :
    X.aut.hom ≫ (f.hom ≫ g.hom) = (f.hom ≫ g.hom) ≫ Z.aut.hom := sorry

/-- The identity inertia morphism. -/
private def idHom (X : Inertia C) : Hom X X :=
  Hom.mk (𝟙 X.obj) (idHom_naturality X)

/-- Composition of inertia morphisms. -/
private def compHom {X Y Z : Inertia C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Hom.mk (f.hom ≫ g.hom) (compHom_naturality f g)

/-- Left identity for inertia morphisms.

Proof strategy: apply `Hom.ext` and use the left identity in `C`. -/
private theorem idHom_comp {X Y : Inertia C} (f : Hom X Y) :
    compHom (idHom X) f = f := sorry

/-- Right identity for inertia morphisms.

Proof strategy: apply `Hom.ext` and use the right identity in `C`. -/
private theorem compHom_id {X Y : Inertia C} (f : Hom X Y) :
    compHom f (idHom Y) = f := sorry

/-- Associativity for inertia morphisms.

Proof strategy: apply `Hom.ext` and use associativity in `C`. -/
private theorem compHom_assoc {W X Y Z : Inertia C}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    compHom (compHom f g) h = compHom f (compHom g h) := sorry

end Implementation

/-- The identity intertwiner has the underlying identity arrow. -/
def Hom.id (X : Inertia C) : Hom X X := Implementation.idHom X

/-- Composition of intertwiners has the underlying composite arrow. -/
def Hom.comp {X Y Z : Inertia C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Implementation.compHom f g

/-- Objects with automorphisms and their intertwiners form the inertia category. -/
instance category : Category (Inertia C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Implementation.idHom_comp
  comp_id := Implementation.compHom_id
  assoc := Implementation.compHom_assoc

attribute [stacks 034I "inertia category structure"] Inertia.category

end

/-- Build an inertia morphism from an underlying arrow and its intertwining equation. -/
@[stacks 034I "construct an abstract inertia morphism"]
def homMk {X Y : Inertia C} (f : X.obj ⟶ Y.obj)
    (naturality : X.aut.hom ≫ f = f ≫ Y.aut.hom) : X ⟶ Y :=
  Hom.mk f naturality

/-- The underlying arrow of an inertia morphism. -/
@[stacks 034I "inertia underlying-arrow projection"]
abbrev hom {X Y : Inertia C} (f : X ⟶ Y) : X.obj ⟶ Y.obj :=
  f.hom

/-- The underlying arrow of an inertia morphism intertwines the chosen automorphisms.

Proof strategy: project the `naturality` field. -/
@[reassoc, stacks 034I "inertia intertwining readout"]
theorem hom.naturality {X Y : Inertia C} (f : X ⟶ Y) :
    X.aut.hom ≫ hom f = hom f ≫ Y.aut.hom := sorry

/-- The underlying arrow of an inertia morphism also intertwines the inverse
automorphisms. -/
@[reassoc, stacks 034I "inertia inverse intertwining readout"]
theorem hom.invNaturality {X Y : Inertia C} (f : X ⟶ Y) :
    X.aut.inv ≫ hom f = hom f ≫ Y.aut.inv := sorry

/-- Inertia morphisms are determined by their underlying arrows.

Proof strategy: apply `Hom.ext`. -/
@[ext, stacks 034I "inertia underlying-arrow extensionality"]
theorem hom_ext {X Y : Inertia C} (f g : X ⟶ Y) (h : hom f = hom g) : f = g := sorry

/-- The underlying arrow of an identity inertia morphism is an identity.

Proof strategy: unfold the category instance. -/
@[simp, stacks 034I "inertia identity underlying arrow"]
theorem hom_id (X : Inertia C) : hom (𝟙 X) = 𝟙 X.obj := sorry

/-- The underlying arrow of a composite inertia morphism is the composite of the underlying
arrows.

Proof strategy: unfold the category instance. -/
@[simp, stacks 034I "inertia composition underlying arrow"]
theorem hom_comp {X Y Z : Inertia C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- An inertia morphism is invertible when its underlying arrow is invertible.

Proof strategy: lift the inverse underlying arrow with `homMk` and verify the two equations by
`hom_ext`. -/
@[stacks 034I "inertia invertibility from underlying arrow"]
theorem isIso_of_hom_isIso {X Y : Inertia C} (f : X ⟶ Y) [IsIso (hom f)] : IsIso f := sorry

/-- An inverse ambient arrow automatically intertwines the automorphisms in the reverse
direction when the forward arrow does. -/
@[stacks 034I "inertia inverse intertwining from an isomorphism"]
theorem isoMk.inv.naturality {X Y : Inertia C}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    Y.aut.hom ≫ e.inv = e.inv ≫ X.aut.hom := sorry

/-- The inertia morphisms induced by the two directions of a compatible ambient isomorphism
compose to the identity on the source. -/
@[stacks 034I "inertia isomorphism hom-inverse law"]
theorem isoMk.hom_inv_id {X Y : Inertia C}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    homMk e.hom naturality ≫
      homMk e.inv (isoMk.inv.naturality e naturality) = 𝟙 X := sorry

/-- The inertia morphisms induced by the two directions of a compatible ambient isomorphism
compose to the identity on the target. -/
@[stacks 034I "inertia isomorphism inverse-hom law"]
theorem isoMk.inv_hom_id {X Y : Inertia C}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    homMk e.inv (isoMk.inv.naturality e naturality) ≫
      homMk e.hom naturality = 𝟙 Y := sorry

/-- Package an ambient isomorphism compatible with the chosen automorphisms as an isomorphism
in the inertia category. The ambient isomorphism is the sole non-`Prop` data owner. -/
@[stacks 034I "construct an abstract inertia isomorphism"]
def isoMk {X Y : Inertia C}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    X ≅ Y where
  hom := homMk e.hom naturality
  inv := homMk e.inv (isoMk.inv.naturality e naturality)
  hom_inv_id := isoMk.hom_inv_id e naturality
  inv_hom_id := isoMk.inv_hom_id e naturality

/-- The underlying forward arrow of `Inertia.isoMk` is the supplied ambient forward arrow. -/
@[simp, stacks 034I "abstract inertia isomorphism forward arrow"]
theorem isoMk.hom {X Y : Inertia C}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    Inertia.hom (isoMk e naturality).hom = e.hom := sorry

/-- The underlying inverse arrow of `Inertia.isoMk` is the supplied ambient inverse arrow. -/
@[simp, stacks 034I "abstract inertia isomorphism inverse arrow"]
theorem isoMk.inv {X Y : Inertia C}
    (e : X.obj ≅ Y.obj)
    (naturality : X.aut.hom ≫ e.hom = e.hom ≫ Y.aut.hom) :
    Inertia.hom (isoMk e naturality).inv = e.inv := sorry

/-- Forget the automorphism from the inertia category. -/
@[stacks 042H "abstract inertia forgetful functor"]
def forget (C : Type uC) [Category.{vC} C] : Inertia C ⥤ C where
  obj X := X.obj
  map f := hom f
  map_id := hom_id
  map_comp := hom_comp

section IdentitySection

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The identity automorphism at an object of `C`. -/
private def identitySectionObj (X : C) : Inertia C := Inertia.mk X 1

/-- Every arrow intertwines the identity automorphisms at its endpoints.

Proof strategy: simplify the identity automorphisms and unit composites. -/
private theorem identitySectionMap_naturality {X Y : C} (f : X ⟶ Y) :
    (identitySectionObj X).aut.hom ≫ f = f ≫ (identitySectionObj Y).aut.hom := sorry

/-- The inertia morphism selected by the identity section. -/
private def identitySectionMap {X Y : C} (f : X ⟶ Y) :
    identitySectionObj X ⟶ identitySectionObj Y :=
  homMk f (identitySectionMap_naturality f)

/-- The identity section preserves identities.

Proof strategy: apply `hom_ext`; both underlying arrows are identities. -/
private theorem identitySectionMap_id (X : C) :
    identitySectionMap (𝟙 X) = 𝟙 (identitySectionObj X) := sorry

/-- The identity section preserves composition.

Proof strategy: apply `hom_ext`; both underlying arrows are the same composite. -/
private theorem identitySectionMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    identitySectionMap (f ≫ g) = identitySectionMap f ≫ identitySectionMap g := sorry

end Implementation

/-- The identity section `C ⥤ Inertia C`. -/
@[stacks 04Z3 "abstract inertia neutral section"]
def identitySection (C : Type uC) [Category.{vC} C] : C ⥤ Inertia C where
  obj := Implementation.identitySectionObj
  map := Implementation.identitySectionMap
  map_id := Implementation.identitySectionMap_id
  map_comp := Implementation.identitySectionMap_comp

/-- The identity section retains the underlying object. -/
@[simp, stacks 04Z3 "abstract inertia identity-section object"]
theorem identitySection.obj.underlying (X : C) :
    ((identitySection C).obj X).obj = X := sorry

/-- The identity section equips an object with its identity automorphism. -/
@[simp, stacks 04Z3 "abstract inertia identity automorphism"]
theorem identitySection.obj.aut (X : C) :
    ((identitySection C).obj X).aut = 1 := sorry

/-- The identity section retains the underlying arrow. -/
@[simp, stacks 04Z3 "abstract inertia identity-section arrow"]
theorem identitySection.map.hom {X Y : C} (f : X ⟶ Y) :
    Inertia.hom ((identitySection C).map f) = f := sorry

end IdentitySection

/-- The identity section followed by the forgetful functor is the identity.

Proof strategy: apply functor extensionality; both object and morphism maps are identities. -/
@[simp, stacks 04Z3 "abstract inertia identity-section round trip"]
theorem identitySection.comp_forget (C : Type uC) [Category.{vC} C] :
    identitySection C ⋙ forget C = 𝟭 C := sorry

section Map

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- A functor maps an inertia object by applying its object and isomorphism maps. -/
private def mapObj (G : C ⥤ D) (X : Inertia C) : Inertia D :=
  Inertia.mk (G.obj X.obj) (G.mapIso X.aut)

/-- A functor maps an intertwiner to an intertwiner.

Proof strategy: apply `G.map` to `hom.naturality` and rewrite by functoriality. -/
private theorem mapHom_naturality (G : C ⥤ D) {X Y : Inertia C} (f : X ⟶ Y) :
    (mapObj G X).aut.hom ≫ G.map (hom f) =
      G.map (hom f) ≫ (mapObj G Y).aut.hom := sorry

/-- The inertia morphism obtained by applying a functor. -/
private def mapHom (G : C ⥤ D) {X Y : Inertia C} (f : X ⟶ Y) :
    mapObj G X ⟶ mapObj G Y :=
  homMk (G.map (hom f)) (mapHom_naturality G f)

/-- Mapping inertia morphisms preserves identities.

Proof strategy: apply `hom_ext` and use `G.map_id`. -/
private theorem mapHom_id (G : C ⥤ D) (X : Inertia C) :
    mapHom G (𝟙 X) = 𝟙 (mapObj G X) := sorry

/-- Mapping inertia morphisms preserves composition.

Proof strategy: apply `hom_ext` and use `G.map_comp`. -/
private theorem mapHom_comp (G : C ⥤ D) {X Y Z : Inertia C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapHom G (f ≫ g) = mapHom G f ≫ mapHom G g := sorry

end Implementation

/-- A functor induces a functor between inertia categories. -/
@[stacks 04Z4 "abstract inertia functoriality"]
def map (G : C ⥤ D) : Inertia C ⥤ Inertia D where
  obj := Implementation.mapObj G
  map := Implementation.mapHom G
  map_id := Implementation.mapHom_id G
  map_comp := Implementation.mapHom_comp G

end Map

/-- The induced inertia functor maps underlying objects by the original functor.

Proof strategy: unfold `map` and its object implementation. -/
@[simp, stacks 04Z4 "abstract inertia map on objects"]
theorem map.obj.underlying (G : C ⥤ D) (X : Inertia C) :
    ((map G).obj X).obj = G.obj X.obj := sorry

/-- The induced inertia functor maps automorphisms by `Functor.mapIso`.

Proof strategy: unfold `map` and its object implementation. -/
@[simp, stacks 04Z4 "abstract inertia map on automorphisms"]
theorem map.obj.aut (G : C ⥤ D) (X : Inertia C) :
    ((map G).obj X).aut = G.mapIso X.aut := sorry

/-- The induced inertia functor maps underlying arrows by `Functor.map`.

Proof strategy: unfold `map` and its morphism implementation. -/
@[simp, stacks 04Z4 "abstract inertia map on arrows"]
theorem map.hom (G : C ⥤ D) {X Y : Inertia C} (f : X ⟶ Y) :
    hom ((map G).map f) = G.map (hom f) := sorry

/-- Mapping inertia and then forgetting agrees with forgetting and applying the original functor.

Proof strategy: apply functor extensionality and use `map.obj.underlying` and `map.hom`. -/
@[stacks 04Z4 "abstract inertia map forgetful compatibility"]
theorem map.comp_forget (G : C ⥤ D) :
    map G ⋙ forget D = forget C ⋙ G := sorry

end Inertia

end CategoryTheory
