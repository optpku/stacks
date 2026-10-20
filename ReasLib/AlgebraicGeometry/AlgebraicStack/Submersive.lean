/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Submersive morphisms of algebraic stacks

A morphism of algebraic stacks is submersive when it induces a quotient map on
underlying point spaces, and universally submersive when every 2-fibre-product
base change is submersive. The defining quotient-map property uses the canonical
topology on points, with a comparison to any topology satisfying its atlas characterization.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The map on points induced by `f` is a quotient map with respect to the given
topologies on the source and target point spaces. -/
def isQuotientMapOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @Topology.IsQuotientMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being a quotient map on points means the induced map is coinducing and
surjective for the given topologies. -/
theorem isQuotientMapOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isQuotientMapOnPoints τX τY f ↔
      @Topology.IsCoinducing (Points X) (Points Y) τX τY (Points.map f) ∧
        Function.Surjective (Points.map f) :=
  sorry

/-- A morphism of algebraic stacks induces a quotient map on canonical point
spaces. -/
def pointsIsQuotientMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  isQuotientMapOnPoints (Points.topology X) (Points.topology Y) f

/-- A morphism induces a quotient map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsQuotientMap_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    pointsIsQuotientMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isQuotientMapOnPoints τX τY f :=
  sorry

/-- A morphism of algebraic stacks is submersive if the induced map on
underlying point spaces is a quotient map. This is distinct from a submersion
of differential manifolds. -/
@[mk_iff]
class Submersive {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is a quotient map for the canonical
  topologies. -/
  isQuotientMap : pointsIsQuotientMap f

namespace Submersive

/-- The identity morphism of an algebraic stack is submersive. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Submersive (𝟙 X) :=
  sorry

/-- A submersive morphism induces a quotient map on points for any pair of
canonical topologies. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Submersive f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isQuotientMapOnPoints τX τY f :=
  sorry

/-- A morphism is submersive as soon as it induces a quotient map on canonical
point spaces. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : pointsIsQuotientMap f) : Submersive f :=
  sorry

end Submersive

/-- A morphism of algebraic stacks is universally submersive if every
2-fibre-product base change induces a quotient map on underlying point
spaces. -/
@[mk_iff]
class UniversallySubmersive {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` is a submersive morphism. -/
  submersive_baseChange {Z P : GroupoidsOver S}
      [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g) :
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Submersive snd

namespace UniversallySubmersive

/-- The identity morphism of an algebraic stack is universally submersive. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversallySubmersive (𝟙 X) :=
  sorry

/-- A universally submersive morphism has submersive 2-fibre-product base
changes. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallySubmersive f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : Submersive snd :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally
submersive morphism `f : X ⟶ Y` is submersive. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallySubmersive f] :
    Submersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallySubmersive

/-- A universally submersive morphism of algebraic stacks is submersive. -/
instance instSubmersive_of_universallySubmersive {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversallySubmersive f] : Submersive f :=
  sorry

/-- A submersive morphism of algebraic stacks is surjective. -/
instance instSurjective_of_submersive {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Submersive f] : Surjective f :=
  sorry

/-- A morphism of algebraic stacks is universally submersive if and only if
every chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` is submersive. -/
theorem universallySubmersive_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallySubmersive f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        Submersive (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
