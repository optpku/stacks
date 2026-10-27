/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Right
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

/-!
# Closed morphisms of algebraic stacks

A morphism is closed when its map on canonical point spaces is closed, and
universally closed when every algebraic-stack base change is closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The map on points induced by `f` is a closed map with respect to the given
topologies on the source and target point spaces. -/
def isClosedMapOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @IsClosedMap (Points X) (Points Y) τX τY (Points.map f)

/-- Being a closed map on points means closed sets in the source point space have
closed images in the target. -/
theorem isClosedMapOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isClosedMapOnPoints τX τY f ↔
      ∀ (U : Set (Points X)),
        @IsClosed (Points X) τX U →
          @IsClosed (Points Y) τY (Points.map f '' U) :=
  Iff.rfl

/-- A morphism of algebraic stacks induces a closed map on canonical point
spaces. -/
def pointsIsClosedMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  isClosedMapOnPoints (Points.topology X) (Points.topology Y) f

/-- A morphism induces a closed map on points if it does so for every pair of
canonical topologies on the source and target. -/
theorem pointsIsClosedMap_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    pointsIsClosedMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isClosedMapOnPoints τX τY f :=
  by
    constructor
    · intro hf τX τY hX hY
      have hτX := isPointsTopology_unique hX (isPointsTopology_pointsTopology X)
      have hτY := isPointsTopology_unique hY (isPointsTopology_pointsTopology Y)
      subst τX
      subst τY
      exact hf
    · intro hf
      exact hf (Points.topology X) (Points.topology Y)
        (isPointsTopology_pointsTopology X) (isPointsTopology_pointsTopology Y)

/-- A morphism of algebraic stacks is closed if the induced map on underlying
point spaces is a closed map. -/
@[mk_iff]
class Closed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- The map on points induced by `f` is closed in the canonical topologies. -/
  isClosedMap : pointsIsClosedMap f

namespace Closed

/-- The identity morphism of an algebraic stack is closed. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Closed (𝟙 X) :=
  by
    constructor
    intro U hU
    simpa only [Points.map_id, Set.image_id'] using hU

/-- A closed morphism induces a closed map on points for any pair of canonical
topologies. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Closed f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isClosedMapOnPoints τX τY f :=
  (pointsIsClosedMap_iff f).mp (Closed.isClosedMap (f := f)) τX τY hX hY

end Closed

private theorem points_map_eq_of_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (e : f ≅ g)
    (x : Points X) : Points.map f x = Points.map g x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  apply Quotient.sound
  refine ⟨⟨p.map f, FieldValuedPoint.Factorization.refl (p.map f), ?_⟩⟩
  refine ⟨𝟙 _, Category.id_comp _, ?_⟩
  exact (FieldValuedPoint.Factorization.refl (p.map g)).fac_iso ≪≫
    Bicategory.whiskerLeftIso p.hom e.symm

private theorem closed_of_equivalenceOnHom {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} (e : Bicategory.Equivalence.OnHom f) : Closed f := by
  have hleft (x : Points X) : Points.map e.inv (Points.map f x) = x := by
    calc
      Points.map e.inv (Points.map f x) = Points.map (f ≫ e.inv) x :=
        (Points.map_comp f e.inv x).symm
      _ = Points.map (𝟙 X) x := points_map_eq_of_iso e.unit.symm x
      _ = x := Points.map_id x
  have hright (y : Points Y) : Points.map f (Points.map e.inv y) = y := by
    calc
      Points.map f (Points.map e.inv y) = Points.map (e.inv ≫ f) y :=
        (Points.map_comp e.inv f y).symm
      _ = Points.map (𝟙 Y) y := points_map_eq_of_iso e.counit y
      _ = y := Points.map_id y
  constructor
  intro U hU
  have himage : Points.map f '' U = Points.map e.inv ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, hleft] using hx
    · intro hy
      exact ⟨Points.map e.inv y, hy, hright y⟩
  rw [himage]
  exact hU.preimage (Points.continuous_map e.inv)

private theorem closed_of_equivalence_comparison {S : Scheme.{u}}
    {X X' Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    [AlgebraicStack Y] (e : X ≌ X') {f : X ⟶ Y} {g : X' ⟶ Y}
    (i : e.hom ≫ g ≅ f) (hg : Closed g) : Closed f := by
  have he := closed_of_equivalenceOnHom (Bicategory.Equivalence.OnHom.ofEquivalence e)
  have hmap : Points.map f = fun x ↦ Points.map g (Points.map e.hom x) := by
    funext x
    exact (points_map_eq_of_iso i x).symm.trans (Points.map_comp e.hom g x)
  constructor
  intro U hU
  rw [hmap]
  simpa only [Set.image_image] using
    hg.isClosedMap (Points.map e.hom '' U) (he.isClosedMap U hU)

/-- A morphism of algebraic stacks is universally closed if every 2-fibre-product
base change induces a closed map on underlying point spaces. -/
@[mk_iff]
class UniversallyClosed {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` is a closed morphism. -/
  closed_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g) :
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd

namespace UniversallyClosed

/-- The identity morphism of an algebraic stack is universally closed. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversallyClosed (𝟙 X) :=
  by
    constructor
    intro Z P hZ hP g fst snd iso h
    let c := Bicategory.PseudoPullbackCone.mk (𝟙 X) g P fst snd iso
    letI : c.IsBilimit := h
    exact closed_of_equivalenceOnHom
      (Bicategory.PseudoPullbackCone.sndEquivalence c (Bicategory.Equivalence.OnHom.id X))

/-- A universally closed morphism has closed 2-fibre-product base changes. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversallyClosed f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : Closed snd :=
  UniversallyClosed.closed_baseChange iso h

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universally closed
morphism `f : X ⟶ Y` is closed. -/
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversallyClosed f] :
    Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  UniversallyClosed.spec (TwoFibreProduct.comparisonIso f g)
    (TwoFibreProduct.cone.isBilimit f g)

end UniversallyClosed

/-- A universally closed morphism of algebraic stacks is closed. -/
instance instClosed_of_universallyClosed {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversallyClosed f] : Closed f :=
  by
    let c := Bicategory.PseudoPullbackCone.ofRightEquivalence f
      (Bicategory.Equivalence.OnHom.id Y)
    letI : AlgebraicStack c.pt := (inferInstance : AlgebraicStack X)
    have hc : Closed c.snd := UniversallyClosed.spec c.iso
      (Bicategory.PseudoPullbackCone.ofRightEquivalence.isBilimit f
        (Bicategory.Equivalence.OnHom.id Y))
    change Closed (f ≫ 𝟙 Y) at hc
    constructor
    intro U hU
    simpa only [Points.map_comp, Points.map_id] using hc.isClosedMap U hU

/-- A morphism of algebraic stacks is universally closed if and only if every
chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` is closed. -/
theorem universallyClosed_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversallyClosed f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  by
    constructor
    · intro hf Z hZ g
      letI := hf
      exact UniversallyClosed.twoFibreProduct_snd g
    · intro hf
      constructor
      intro Z P hZ hP g fst snd iso h
      let c := Bicategory.PseudoPullbackCone.mk f g P fst snd iso
      let d := TwoFibreProduct.cone.{u + 1, u, u + 1, u} f g
      letI : c.IsBilimit := h
      letI : AlgebraicStack c.pt := hP
      letI : AlgebraicStack d.pt := inferInstanceAs
        (AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
      exact closed_of_equivalence_comparison
        (Bicategory.PseudoPullbackCone.apexEquivalence c d)
        (Bicategory.PseudoPullbackCone.apexEquivalence.homSndIso c d) (hf g)

end AlgebraicGeometry.AlgebraicStack

