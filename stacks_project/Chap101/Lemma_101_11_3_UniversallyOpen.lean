module

public import stacks_project.Chap101.Lemma_101_27_15_OpenMap

/-!
# Open and universally open morphisms of algebraic stacks

A morphism of algebraic stacks is open when it induces an open map on
underlying point spaces, and universally open when every 2-fibre-product
base change is open. Competing canonical topologies on `Points` remain
explicit parameters, parallel to `Closed` and `UniversallyClosed`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is open if the induced map on underlying
point spaces is an open map. -/
@[mk_iff]
class Open {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is open for every pair of canonical
  topologies. -/
  isOpenMap : pointsIsOpenMap f

namespace Open

/-- The identity morphism of an algebraic stack is open. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Open (𝟙 X) :=
  sorry

/-- An open morphism induces an open map on points for any pair of canonical
topologies. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Open f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isOpenMapOnPoints τX τY f :=
  sorry

/-- A morphism is open as soon as it induces an open map on canonical point
spaces. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : pointsIsOpenMap f) : Open f :=
  sorry

end Open

/-- A morphism of algebraic stacks is universally open if every 2-fibre-product
base change induces an open map on underlying point spaces. -/
@[mk_iff]
class UniversallyOpen {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` is an open morphism. -/
  open_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g) :
      (Points.cone iso).IsBilimit → Open snd

namespace UniversallyOpen

/-- The identity morphism of an algebraic stack is universally open. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversallyOpen (𝟙 X) :=
  sorry

/-- A universally open morphism has open 2-fibre-product base changes. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyOpen f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (Points.cone iso).IsBilimit) : Open snd :=
  sorry

/-- Every 2-fibre-product projection `snd` of a universally open morphism is
open. -/
theorem isOpen_of_isBilimit {S : Scheme.{u}} {X Y Z P : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [AlgebraicStack P]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
    [UniversallyOpen f] (iso : fst ≫ f ≅ snd ≫ g)
    (h : (Points.cone iso).IsBilimit) : Open snd :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally open
morphism `f : X ⟶ Y` is open, once the apex is known to be an algebraic
stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyOpen f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Open (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Universally open morphisms of algebraic stacks remain universally open
along the second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallyOpen f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallyOpen c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally open
whenever the second leg is a universally open morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyOpen g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    UniversallyOpen (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallyOpen

/-- A universally open morphism of algebraic stacks is open. -/
instance instOpen_of_universallyOpen {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversallyOpen f] : Open f :=
  sorry

/-- Typeclass form of openness of the chosen 2-fibre-product projection of a
universally open morphism. -/
instance instOpen_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyOpen f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    Open (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- A morphism of algebraic stacks is universally open if and only if every
2-fibre-product base change, expressed by an `IsBilimit` square, is an open
morphism. -/
theorem universallyOpen_iff_isOpen_of_isBilimit {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyOpen f ↔
      ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
        {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
        (iso : fst ≫ f ≅ snd ≫ g),
        (Points.cone iso).IsBilimit → Open snd :=
  sorry

/-- A morphism of algebraic stacks is universally open if and only if every
chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` is open. -/
theorem universallyOpen_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyOpen f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        Open (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
