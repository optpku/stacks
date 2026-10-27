/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Homeomorph
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Right

/-!
# Universal homeomorphisms of algebraic stacks

A morphism is a universal homeomorphism when every algebraic-stack base change
induces a homeomorphism on underlying point spaces. For morphisms representable
by algebraic spaces, this agrees with the scheme-slice universal-homeomorphism
property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces a homeomorphism of underlying point spaces. -/
def isHomeomorphAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
    AlgebraicStack.pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being a homeomorphism after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` induces a homeomorphism of underlying
point spaces. -/
theorem isHomeomorphAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isHomeomorphAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        AlgebraicStack.pointsIsHomeomorph
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  Iff.rfl

/-- A morphism of algebraic stacks representable by algebraic spaces has the
scheme-slice universal-homeomorphism property if and only if every algebraic-stack
base change induces a homeomorphism on canonical point spaces. The induced map
is the point map of the second 2-fibre-product projection. -/
theorem has_universalHomeomorphism_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversalHomeomorphism S) f ↔
      isHomeomorphAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack

private theorem pointsMap_eq_of_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (i : f ≅ g) :
    Points.map f = Points.map g := by
  funext x
  refine Quotient.inductionOn x ?_
  intro p
  change Points.mk (p.map f) = Points.mk (p.map g)
  apply Quotient.sound
  exact ⟨{
    point := p.map f
    left := FieldValuedPoint.Factorization.refl (p.map f)
    right := {
      schemeHom := 𝟙 _
      fac_structure := Category.id_comp _
      fac_iso := (FieldValuedPoint.Factorization.refl (p.map g)).fac_iso ≪≫
        (Bicategory.whiskerLeftIso p.hom i).symm } }⟩

private theorem pointsIsHomeomorph_iff_of_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (i : f ≅ g) :
    pointsIsHomeomorph f ↔ pointsIsHomeomorph g := by
  change IsHomeomorph (Points.map f) ↔ IsHomeomorph (Points.map g)
  rw [pointsMap_eq_of_iso i]

private theorem pointsIsHomeomorph_of_equivalence {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (e : X ≌ Y) :
    pointsIsHomeomorph e.hom := by
  let h : Points X ≃ₜ Points Y := {
    toFun := Points.map e.hom
    invFun := Points.map e.inv
    left_inv := fun x ↦ by
      calc
        Points.map e.inv (Points.map e.hom x) = Points.map (e.hom ≫ e.inv) x :=
          (Points.map_comp e.hom e.inv x).symm
        _ = Points.map (𝟙 X) x := congrFun (pointsMap_eq_of_iso e.unit.symm) x
        _ = x := Points.map_id x
    right_inv := fun y ↦ by
      calc
        Points.map e.hom (Points.map e.inv y) = Points.map (e.inv ≫ e.hom) y :=
          (Points.map_comp e.inv e.hom y).symm
        _ = Points.map (𝟙 Y) y := congrFun (pointsMap_eq_of_iso e.counit) y
        _ = y := Points.map_id y
    continuous_toFun := Points.continuous_map e.hom
    continuous_invFun := Points.continuous_map e.inv }
  exact h.isHomeomorph

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
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → pointsIsHomeomorph snd

namespace UniversalHomeomorphism

/-- The identity morphism of an algebraic stack is a universal homeomorphism. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversalHomeomorphism (𝟙 X) := by
  constructor
  intro Z P _ _ g fst snd iso h
  letI := h
  exact pointsIsHomeomorph_of_equivalence (X := P) (Y := Z)
    (Bicategory.PseudoPullbackCone.sndEquivalence
      (Bicategory.PseudoPullbackCone.mk (𝟙 X) g P fst snd iso)
      (Bicategory.Equivalence.OnHom.id X)).toEquivalence

/-- The composition of a pair of universal homeomorphisms of algebraic stacks
is a universal homeomorphism. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) :=
  sorry

/-- A universal homeomorphism has 2-fibre-product base changes that induce
homeomorphisms on points. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversalHomeomorphism f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : pointsIsHomeomorph snd :=
  UniversalHomeomorphism.homeomorph_baseChange iso h

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universal
homeomorphism `f : X ⟶ Y` induces a homeomorphism on points, once the apex
is known to be an algebraic stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversalHomeomorphism f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  spec (TwoFibreProduct.comparisonIso f g) (TwoFibreProduct.cone.isBilimit f g)

end UniversalHomeomorphism

/-- A universal homeomorphism of algebraic stacks induces a homeomorphism on
underlying point spaces. -/
theorem pointsIsHomeomorph_of_universalHomeomorphism {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversalHomeomorphism f] : pointsIsHomeomorph f := by
  let c := Bicategory.PseudoPullbackCone.ofRightEquivalence f
    (Bicategory.Equivalence.OnHom.id Y)
  have h : pointsIsHomeomorph (f ≫ 𝟙 Y) :=
    UniversalHomeomorphism.spec c.iso
      (Bicategory.PseudoPullbackCone.ofRightEquivalence.isBilimit f
        (Bicategory.Equivalence.OnHom.id Y))
  exact (pointsIsHomeomorph_iff_of_iso (ρ_ f)).mp h

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
        (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → pointsIsHomeomorph snd :=
  ⟨fun h ↦ h.homeomorph_baseChange, fun h ↦ ⟨h⟩⟩

/-- A morphism of algebraic stacks is a universal homeomorphism if and only if
every chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` induces a
homeomorphism on points. -/
theorem universalHomeomorphism_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) := by
  constructor
  · intro hf Z _ g _
    letI := hf
    exact UniversalHomeomorphism.twoFibreProduct_snd g
  · intro hf
    constructor
    intro Z P _ _ g fst snd iso h
    let c := Bicategory.PseudoPullbackCone.mk f g P fst snd iso
    letI : c.IsBilimit := h
    let d := TwoFibreProduct.cone.{u + 1, u, u + 1, u} f g
    have he := pointsIsHomeomorph_of_equivalence
      (X := P) (Y := TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
      (Bicategory.PseudoPullbackCone.apexEquivalence c d)
    have hd := hf g
    exact (pointsIsHomeomorph_iff_of_iso (X := P) (Y := Z)
      (Bicategory.PseudoPullbackCone.apexEquivalence.homSndIso c d)).mp
        (pointsIsHomeomorph_comp (X := P)
          (Y := TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) (Z := Z) he hd)

end AlgebraicGeometry.AlgebraicStack
