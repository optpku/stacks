module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Immersions of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is an open immersion, a closed immersion, or
an immersion when every representing morphism of algebraic spaces
`fy : Fy ⟶ ofOver U` has the matching algebraic-space immersion property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is an open
immersion when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is an open immersion of algebraic spaces. -/
class OpenImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is an open immersion. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.IsOpenImmersion fy

/-- A 1-morphism of categories fibred in groupoids over `Over S` is a closed
immersion when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is a closed immersion of algebraic spaces. -/
class ClosedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is a closed immersion. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.IsClosedImmersion fy

/-- A 1-morphism of categories fibred in groupoids over `Over S` is an
immersion when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is an immersion of algebraic spaces. -/
class Immersion {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is an immersion. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.IsImmersion fy

namespace OpenImmersion

/-- The identity 1-morphism of a category fibred in groupoids is an open
immersion. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : OpenImmersion (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for an open immersion of
groupoid fibrations is an open immersion. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [OpenImmersion f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsOpenImmersion fy := sorry

/-- An open immersion of groupoid fibrations is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [OpenImmersion f] :
    relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is an open immersion if and only if it is representable by
algebraic spaces and has the algebraic-space open-immersion property in the
sense of scheme-slice tests. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    OpenImmersion f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      has (@AlgebraicSpace.IsOpenImmersion S) f := sorry

/-- An open immersion of groupoid fibrations has the algebraic-space
open-immersion property on scheme-slice representing morphisms. -/
theorem has_isOpenImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [OpenImmersion f] :
    has (@AlgebraicSpace.IsOpenImmersion S) f := sorry

end OpenImmersion

namespace ClosedImmersion

/-- The identity 1-morphism of a category fibred in groupoids is a closed
immersion. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : ClosedImmersion (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for a closed immersion of
groupoid fibrations is a closed immersion. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [ClosedImmersion f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsClosedImmersion fy := sorry

/-- A closed immersion of groupoid fibrations is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [ClosedImmersion f] :
    relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is a closed immersion if and only if it is representable by
algebraic spaces and has the algebraic-space closed-immersion property in the
sense of scheme-slice tests. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    ClosedImmersion f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      has (@AlgebraicSpace.IsClosedImmersion S) f := sorry

/-- A closed immersion of groupoid fibrations has the algebraic-space
closed-immersion property on scheme-slice representing morphisms. -/
theorem has_isClosedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [ClosedImmersion f] :
    has (@AlgebraicSpace.IsClosedImmersion S) f := sorry

end ClosedImmersion

namespace Immersion

/-- The identity 1-morphism of a category fibred in groupoids is an
immersion. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Immersion (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for an immersion of groupoid
fibrations is an immersion. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Immersion f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsImmersion fy := sorry

/-- An immersion of groupoid fibrations is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Immersion f] :
    relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is an immersion if and only if it is representable by
algebraic spaces and has the algebraic-space immersion property in the sense
of scheme-slice tests. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Immersion f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      has (@AlgebraicSpace.IsImmersion S) f := sorry

/-- An immersion of groupoid fibrations has the algebraic-space immersion
property on scheme-slice representing morphisms. -/
theorem has_isImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Immersion f] : has (@AlgebraicSpace.IsImmersion S) f := sorry

/-- An open immersion of groupoid fibrations is an immersion. -/
instance of_openImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [OpenImmersion f] : Immersion f := sorry

/-- A closed immersion of groupoid fibrations is an immersion. -/
instance of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [ClosedImmersion f] : Immersion f := sorry

end Immersion

end AlgebraicGeometry.Groupoids.Hom
