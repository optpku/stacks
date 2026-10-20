module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.OpenMap
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Open and universally open morphisms of algebraic stacks

Openness is defined on canonical point spaces. Universal openness requires
openness after every algebraic-stack base change, expressed by a bilimit square.
-/

@[expose] public section

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
  /-- The induced map on points is open for the canonical point topologies. -/
  isOpenMap : pointsIsOpenMap f

namespace Open

/-- The composition of two open morphisms of algebraic stacks is open. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Open f] [Open g] :
    Open (f ≫ g) :=
  sorry

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

/-- A morphism is open if its induced map on canonical point spaces is open. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : pointsIsOpenMap f) : Open f :=
  ⟨hf⟩

end Open

/-- A morphism of algebraic stacks is universally open if every 2-fibre-product
base change induces an open map on underlying point spaces. -/
@[mk_iff]
class UniversallyOpen {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of the morphism is open. -/
  open_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g) :
      (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Open snd

namespace UniversallyOpen

/-- The composition of two universally open morphisms of algebraic stacks is
universally open. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyOpen f] [UniversallyOpen g] :
    UniversallyOpen (f ≫ g) :=
  sorry

/-- The identity morphism of an algebraic stack is universally open. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversallyOpen (𝟙 X) :=
  sorry

/-- A universally open morphism has open 2-fibre-product base changes. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyOpen f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : Open snd :=
  UniversallyOpen.open_baseChange iso h

/-- The second projection of a chosen 2-fibre product of a universally open
morphism is open. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyOpen f] :
    Open (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- Universally open morphisms remain universally open along the second
projection of any algebraic-stack bilimit square. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [UniversallyOpen f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    UniversallyOpen c.snd :=
  sorry

/-- The first projection of a chosen 2-fibre product is universally open
whenever the second leg is universally open. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyOpen g] :
    UniversallyOpen (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallyOpen

/-- A universally open morphism of algebraic stacks is open. -/
instance instOpen_of_universallyOpen {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversallyOpen f] : Open f :=
  sorry

/-- A morphism of algebraic stacks is universally open if and only if every
chosen second 2-fibre-product projection is open. -/
theorem universallyOpen_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyOpen f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        Open (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The base change of a universally open morphism of algebraic stacks along
any morphism of algebraic stacks is universally open. -/
instance universallyOpen_pullback_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyOpen f] :
    UniversallyOpen (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  @UniversallyOpen.of_isBilimit S X Y Z _ _ _ f g _
    (TwoFibreProduct.cone f g) (instTwoFibreProduct (f := f) (g := g))
    (TwoFibreProduct.cone.isBilimit f g)

end AlgebraicGeometry.AlgebraicStack
