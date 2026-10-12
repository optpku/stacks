/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Smooth and surjective morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is smooth (resp. surjective) when every
representing morphism of algebraic spaces `Fy ⟶ ofOver U` is smooth
(resp. surjective).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is smooth when
it is representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is a smooth morphism of algebraic spaces. -/
class Smooth {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is smooth. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Smooth fy

/-- A 1-morphism of categories fibred in groupoids over `Over S` is surjective
when it is representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is a surjective morphism of algebraic spaces. -/
class Surjective {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is surjective. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Surjective fy

namespace Smooth

/-- The identity 1-morphism of a category fibred in groupoids is smooth. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Smooth (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a smooth 1-morphism is
smooth. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Smooth f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.Smooth fy := sorry

/-- A smooth 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Smooth f] : relativelyRepresentableByAlgebraicSpaces f := sorry

end Smooth

namespace Surjective

/-- The identity 1-morphism of a category fibred in groupoids is surjective. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Surjective (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a surjective 1-morphism is
surjective. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Surjective f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.Surjective fy := sorry

/-- A surjective 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Surjective f] : relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end Surjective

end AlgebraicGeometry.Groupoids.Hom
