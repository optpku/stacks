module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Affine morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is affine when every representing morphism
of algebraic spaces `fy : Fy ⟶ ofOver U` is an affine morphism of algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is affine when
it is representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is an affine morphism of algebraic spaces. -/
class Affine {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is affine. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Affine fy

namespace Affine

/-- The identity 1-morphism of a category fibred in groupoids is affine. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Affine (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for an affine 1-morphism is
affine. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Affine f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.Affine fy := sorry

/-- An affine 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Affine f] : relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is affine if and only if it is representable by algebraic
spaces and has the algebraic-space affine property in the sense of
scheme-slice tests. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Affine f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      has (@AlgebraicSpace.Affine S) f := sorry

/-- An affine 1-morphism has the algebraic-space affine property on
scheme-slice representing morphisms. -/
theorem has_affine {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Affine f] : has (@AlgebraicSpace.Affine S) f := sorry

/-- An affine morphism of algebraic spaces induces an affine 1-morphism of the
associated groupoid fibrations. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Affine f] : Affine (AlgebraicSpace.toGroupoids.map f) :=
  sorry

/-- The composite of two affine 1-morphisms of groupoid fibrations is affine. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [hf : Affine f] [hg : Affine g] :
    Affine (f ≫ g) := sorry

/-- Affine 1-morphisms of groupoid fibrations over a scheme are stable under
composition as a morphism property. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Affine S : MorphismProperty (GroupoidsOver S)) where
  comp_mem f g hf hg := comp f g (hf := hf) (hg := hg)

end Affine

end AlgebraicGeometry.Groupoids.Hom
