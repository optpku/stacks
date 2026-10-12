/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones

/-!
# Preorder transitions with adjoined identities

Original preorder transitions, including reflexive transitions, are retained as
arrows distinct from the adjoined categorical identities.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

/-- The objects of a preorder, with categorical identities adjoined to its transitions. -/
def PreorderWithAdjoinedIdentities (I : Type u) : Type u := I

namespace PreorderWithAdjoinedIdentities

variable {I : Type u} [Preorder I]

/-- Morphisms are equality arrows together with the original preorder transitions. -/
def Hom (first second : PreorderWithAdjoinedIdentities I) : Type :=
  PLift (first = second) ⊕ PLift (LE.le (α := I) first second)

/-- The adjoined categorical identity at a preorder object. -/
def id (index : PreorderWithAdjoinedIdentities I) : Hom index index :=
  Sum.inl ⟨rfl⟩

/-- Composition transports along equalities and composes preorder transitions transitively. -/
def comp {first second third : PreorderWithAdjoinedIdentities I}
    (firstArrow : Hom first second) (secondArrow : Hom second third) : Hom first third :=
  match firstArrow, secondArrow with
  | Sum.inl ⟨rfl⟩, arrow => arrow
  | Sum.inr inequality, Sum.inl ⟨rfl⟩ => Sum.inr inequality
  | Sum.inr firstLe, Sum.inr secondLe => Sum.inr ⟨le_trans firstLe.down secondLe.down⟩

/-- Left composition by an adjoined identity is trivial. -/
theorem id_comp {first second : PreorderWithAdjoinedIdentities I} (arrow : Hom first second) :
    comp (id first) arrow = arrow := sorry

/-- Right composition by an adjoined identity is trivial. -/
theorem comp_id {first second : PreorderWithAdjoinedIdentities I} (arrow : Hom first second) :
    comp arrow (id second) = arrow := sorry

/-- Composition of preorder transitions with adjoined identities is associative. -/
theorem assoc {first second third fourth : PreorderWithAdjoinedIdentities I}
    (firstArrow : Hom first second) (secondArrow : Hom second third)
    (thirdArrow : Hom third fourth) :
    comp (comp firstArrow secondArrow) thirdArrow =
      comp firstArrow (comp secondArrow thirdArrow) := sorry

/-- Equality arrows compose by transport, and transition arrows compose by transitivity. -/
instance category : Category.{0} (PreorderWithAdjoinedIdentities I) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := fun arrow => id_comp arrow
  comp_id := fun arrow => comp_id arrow
  assoc := fun firstArrow secondArrow thirdArrow => assoc firstArrow secondArrow thirdArrow

/-- The original transition associated to an inequality, distinct from an adjoined identity. -/
def transition {first second : PreorderWithAdjoinedIdentities I}
    (inequality : LE.le (α := I) first second) : first ⟶ second :=
  Sum.inr ⟨inequality⟩

/-- Adjoining identities to the transitions of a nonempty directed preorder gives a filtered
category. -/
instance isFiltered [Nonempty I] [IsDirected I (· ≤ ·)] :
    IsFiltered (PreorderWithAdjoinedIdentities I) := sorry

variable {C : Type v} [Category.{w} C]

/-- The map assigned by the lifted functor to an equality or preorder arrow. -/
def liftMap (objects : I → C)
    (maps : ∀ {first second : I}, first ≤ second → (objects first ⟶ objects second))
    (maps_comp : ∀ {first second third : I} (firstLe : first ≤ second)
      (secondLe : second ≤ third),
      maps (le_trans firstLe secondLe) = maps firstLe ≫ maps secondLe)
    {first second : PreorderWithAdjoinedIdentities I} (arrow : Hom first second) :
    objects first ⟶ objects second :=
  match arrow with
  | Sum.inl equality => eqToHom (congrArg objects equality.down)
  | Sum.inr inequality => maps inequality.down

/-- The lifted arrow map preserves identities. -/
theorem liftMap_id (objects : I → C)
    (maps : ∀ {first second : I}, first ≤ second → (objects first ⟶ objects second))
    (maps_comp : ∀ {first second third : I} (firstLe : first ≤ second)
      (secondLe : second ≤ third),
      maps (le_trans firstLe secondLe) = maps firstLe ≫ maps secondLe)
    (index : I) :
    liftMap objects maps maps_comp (id index) = 𝟙 (objects index) := sorry

/-- The lifted arrow map preserves composition. -/
theorem liftMap_comp (objects : I → C)
    (maps : ∀ {first second : I}, first ≤ second → (objects first ⟶ objects second))
    (maps_comp : ∀ {first second third : I} (firstLe : first ≤ second)
      (secondLe : second ≤ third),
      maps (le_trans firstLe secondLe) = maps firstLe ≫ maps secondLe)
    {first second third : PreorderWithAdjoinedIdentities I}
    (firstArrow : Hom first second) (secondArrow : Hom second third) :
    liftMap objects maps maps_comp (comp firstArrow secondArrow) =
      liftMap objects maps maps_comp firstArrow ≫ liftMap objects maps maps_comp secondArrow := sorry

/-- Composition-compatible transition maps extend to a functor by sending equality arrows
to equality transport and original transitions to the supplied maps. -/
def lift (objects : I → C)
    (maps : ∀ {first second : I}, first ≤ second → (objects first ⟶ objects second))
    (maps_comp : ∀ {first second third : I} (firstLe : first ≤ second)
      (secondLe : second ≤ third),
      maps (le_trans firstLe secondLe) = maps firstLe ≫ maps secondLe) :
    PreorderWithAdjoinedIdentities I ⥤ C where
  obj := objects
  map := liftMap objects maps maps_comp
  map_id := fun index => liftMap_id objects maps maps_comp index
  map_comp := fun firstArrow secondArrow => liftMap_comp objects maps maps_comp firstArrow secondArrow

/-- The lifted functor sends each original transition to its supplied map. -/
theorem lift_map_transition (objects : I → C)
    (maps : ∀ {first second : I}, first ≤ second → (objects first ⟶ objects second))
    (maps_comp : ∀ {first second third : I} (firstLe : first ≤ second)
      (secondLe : second ≤ third),
      maps (le_trans firstLe secondLe) = maps firstLe ≫ maps secondLe)
    {first second : I} (inequality : first ≤ second) :
    (lift objects maps maps_comp).map (transition inequality) = maps inequality := sorry

/-- Cocone naturality for a lifted diagram is equivalent to compatibility with precisely
the original preorder transitions. -/
theorem lift_cocone_iff (objects : I → C)
    (maps : ∀ {first second : I}, first ≤ second → (objects first ⟶ objects second))
    (maps_comp : ∀ {first second third : I} (firstLe : first ≤ second)
      (secondLe : second ≤ third),
      maps (le_trans firstLe secondLe) = maps firstLe ≫ maps secondLe)
    (vertex : C) (legs : ∀ index : I, objects index ⟶ vertex) :
    (∀ {first second : PreorderWithAdjoinedIdentities I} (arrow : first ⟶ second),
      (lift objects maps maps_comp).map arrow ≫ legs second = legs first) ↔
      ∀ {first second : I} (inequality : first ≤ second),
        maps inequality ≫ legs second = legs first := sorry

end PreorderWithAdjoinedIdentities

end CategoryTheory
