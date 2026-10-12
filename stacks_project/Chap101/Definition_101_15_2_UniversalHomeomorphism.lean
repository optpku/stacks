/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_15_1_Homeomorph

/-!
# Universal homeomorphisms of algebraic stacks

A morphism of algebraic stacks is a universal homeomorphism when every
2-fibre-product base change induces a homeomorphism on underlying point
spaces. Competing canonical topologies on `Points` remain explicit
parameters, parallel to `UniversallyClosed` and `UniversallyOpen`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is a universal homeomorphism if every
2-fibre-product base change induces a homeomorphism on underlying point
spaces. -/
@[mk_iff]
class UniversalHomeomorphism {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` induces a homeomorphism on
  points. -/
  homeomorph_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z]
      [AlgebraicStack P] {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
      (iso : fst ≫ f ≅ snd ≫ g) :
      (Points.cone iso).IsBilimit → pointsIsHomeomorph snd

namespace UniversalHomeomorphism

/-- The identity morphism of an algebraic stack is a universal homeomorphism. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversalHomeomorphism (𝟙 X) :=
  sorry

/-- A universal homeomorphism has 2-fibre-product base changes that induce
homeomorphisms on points. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversalHomeomorphism f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (Points.cone iso).IsBilimit) : pointsIsHomeomorph snd :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universal
homeomorphism `f : X ⟶ Y` induces a homeomorphism on points, once the apex
is known to be an algebraic stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversalHomeomorphism f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversalHomeomorphism

/-- A universal homeomorphism of algebraic stacks induces a homeomorphism on
underlying point spaces. -/
theorem pointsIsHomeomorph_of_universalHomeomorphism {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversalHomeomorphism f] : pointsIsHomeomorph f :=
  sorry

/-- A morphism of algebraic stacks is a universal homeomorphism if and only if
every 2-fibre-product base change, expressed by an `IsBilimit` square,
induces a homeomorphism on points. -/
theorem universalHomeomorphism_iff_pointsIsHomeomorph_of_isBilimit
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
        {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
        (iso : fst ≫ f ≅ snd ≫ g),
        (Points.cone iso).IsBilimit → pointsIsHomeomorph snd :=
  sorry

/-- A morphism of algebraic stacks is a universal homeomorphism if and only if
every chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` induces a
homeomorphism on points. -/
theorem universalHomeomorphism_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
