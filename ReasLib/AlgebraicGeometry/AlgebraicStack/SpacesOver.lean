/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable.Faithful

/-!
# The 2-category of algebraic spaces over an algebraic stack

For an algebraic stack `Y`, `SpacesOver Y` is the full sub-2-category of the
pseudo slice over `Y` on morphisms of algebraic stacks that are representable
by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace SpacesOver

/-- The object property on the pseudo slice over an algebraic stack `Y` selecting
morphisms of algebraic stacks that are representable by algebraic spaces. -/
def objectProperty {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y] :
    ObjectProperty (Bicategory.PseudoSlice Y) :=
  fun P ↦
    AlgebraicStack (Bicategory.PseudoCostructuredArrow.left P) ∧
      relativelyRepresentableByAlgebraicSpaces
        (Bicategory.PseudoCostructuredArrow.hom P)

end SpacesOver

/-- The 2-category of morphisms `f : X ⟶ Y` of algebraic stacks that are
representable by algebraic spaces. -/
abbrev SpacesOver {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y] :=
  (SpacesOver.objectProperty Y).FullSubbicategory

namespace SpacesOver

/-- The pseudo-slice object of a representable morphism of algebraic stacks
satisfies the selecting property of `SpacesOver`. -/
theorem objectProperty_mk {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    objectProperty Y (Bicategory.PseudoCostructuredArrow.mk X f) := by
  change AlgebraicStack X ∧ relativelyRepresentableByAlgebraicSpaces f
  exact ⟨inferInstance, hf⟩

/-- Package a morphism of algebraic stacks representable by algebraic spaces as an
object of `SpacesOver Y`. -/
def mk {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) : SpacesOver Y :=
  ObjectProperty.FullSubbicategory.mk (objectProperty Y)
    (Bicategory.PseudoCostructuredArrow.mk X f) (objectProperty_mk f hf)

/-- The domain of an object of `SpacesOver Y`. -/
abbrev left {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : SpacesOver Y) : GroupoidsOver S :=
  Bicategory.PseudoCostructuredArrow.left P.1

/-- The structural morphism of an object of `SpacesOver Y`. -/
abbrev hom {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : SpacesOver Y) : left P ⟶ Y :=
  Bicategory.PseudoCostructuredArrow.hom P.1

/-- The domain of an object of `SpacesOver Y` is an algebraic stack. -/
instance instAlgebraicStack_left {S : Scheme.{u}} {Y : GroupoidsOver S}
    [AlgebraicStack Y] (P : SpacesOver Y) : AlgebraicStack (left P) :=
  P.property.1

/-- The domain of a packaged object is the supplied algebraic stack. -/
theorem mk_left {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    left (mk f hf) = X :=
  rfl

/-- The structural morphism of a packaged object is the supplied morphism. -/
theorem mk_hom {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    hom (mk f hf) = f :=
  rfl

/-- An object of `SpacesOver Y` has an algebraic-stack domain and a structural
morphism representable by algebraic spaces. -/
theorem spec {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : SpacesOver Y) :
    AlgebraicStack (left P) ∧ relativelyRepresentableByAlgebraicSpaces (hom P) :=
  P.property

/-- Reconstructing an object of `SpacesOver Y` from its structural morphism
recovers the original object. -/
theorem iff {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (P : SpacesOver Y) :
    ∃ hf : relativelyRepresentableByAlgebraicSpaces (hom P),
      P = mk (hom P) hf := by
  rcases P with ⟨⟨X, ⟨⟨⟨⟩⟩⟩, f⟩, h⟩
  exact ⟨h.2, rfl⟩

/-- Package a morphism `g` of domains together with a comparison isomorphism
`β : hom P ≅ g ≫ hom Q` as a 1-morphism of `SpacesOver Y`. The source cell
`β` is the inverse of the canonical `fac` comparison. -/
def homMk {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    {P Q : SpacesOver Y} (g : left P ⟶ left Q)
    (β : hom P ≅ g ≫ hom Q) : P ⟶ Q :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.PseudoCostructuredArrow.homMk g β.symm)

/-- Hom-categories of `SpacesOver Y` are thin: a 2-morphism between parallel
1-morphisms is unique when it exists, since the target structural morphism is
faithful. -/
instance homIsThin {S : Scheme.{u}} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f1 f2 : SpacesOver Y) : Quiver.IsThin (f1 ⟶ f2) := by
  letI := (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_faithful
    (hom f2)).mp (spec f2).2
  intro f g
  refine ⟨fun η θ => ?_⟩
  apply Bicategory.InducedBicategory.hom₂_ext
  apply ObjectProperty.hom_ext
  apply Bicategory.ColaxComma.Hom₂.ext
  · have hwhisker : η.hom.hom.left ▷ hom f2 = θ.hom.hom.left ▷ hom f2 := by
      apply (cancel_mono (Bicategory.PseudoComma.cell g.hom)).1
      exact η.hom.hom.w.trans θ.hom.hom.w.symm
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext a
    apply (FiberedCategoryOver.Groupoids.toFunctor (hom f2)).map_injective
    exact congrArg (fun ξ => ξ.hom.toNatTrans.app a) hwhisker
  · exact Subsingleton.elim _ _

/-- The 2-category `SpacesOver Y` is a (2,1)-category: every 2-morphism is
invertible. Together with `homIsThin`, each hom-category is a setoid. -/
instance locallyGroupoid {S : Scheme.{u}} {Y : GroupoidsOver S}
    [AlgebraicStack Y] : Bicategory.IsLocallyGroupoid (SpacesOver Y) := by
  letI : Bicategory.IsLocallyGroupoid (GroupoidsOver S) :=
    FiberedCategoryOver.Groupoids.locallyGroupoid
  intro P Q
  constructor
  intro f g η
  letI : IsIso η.hom.hom := Bicategory.ColaxComma.hom₂_isIso η.hom.hom
  letI : IsIso η.hom := (ObjectProperty.isIso_hom_iff η.hom).mp inferInstance
  exact (Bicategory.InducedBicategory.isoMk (asIso η.hom)).isIso_hom

end SpacesOver

end AlgebraicGeometry
