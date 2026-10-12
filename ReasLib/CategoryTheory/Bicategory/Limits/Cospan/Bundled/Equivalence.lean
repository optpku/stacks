/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Equivalence.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Equivalence

/-!
# Vertex equivalences of bundled bicategorical cospans

An equivalence of bundled cospans induces equivalences at the left endpoint, right endpoint,
and common target. They are defined by applying the canonical vertex-projection
pseudofunctors, so their adjoint-equivalence data are inherited from the general
`Pseudofunctor.mapEquivalence` construction.

The API also identifies these projected equivalences with evaluation of the underlying
walking-cospan diagram equivalence.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

/-- The equivalence induced at the left endpoint of two equivalent bundled cospans. -/
@[stacks 0040 "left-endpoint equivalence of bundled bicategorical cospans"]
def leftEquivalence (e : S ≌ T) : S.left ≌ T.left :=
  (leftProjection B).mapEquivalence e

/-- The equivalence induced at the right endpoint of two equivalent bundled cospans. -/
@[stacks 0040 "right-endpoint equivalence of bundled bicategorical cospans"]
def rightEquivalence (e : S ≌ T) : S.right ≌ T.right :=
  (rightProjection B).mapEquivalence e

/-- The equivalence induced at the common target of two equivalent bundled cospans. -/
@[stacks 0040 "common-target equivalence of bundled bicategorical cospans"]
def baseEquivalence (e : S ≌ T) : S.base ≌ T.base :=
  (baseProjection B).mapEquivalence e

/-- The left-endpoint equivalence agrees with evaluation of the underlying diagram
equivalence at the left vertex. -/
@[simp]
theorem leftEquivalence.app (e : S ≌ T) :
    leftEquivalence e =
      (diagramEquivalence e).app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry

/-- The right-endpoint equivalence agrees with evaluation of the underlying diagram
equivalence at the right vertex. -/
@[simp]
theorem rightEquivalence.app (e : S ≌ T) :
    rightEquivalence e =
      (diagramEquivalence e).app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry

/-- The common-target equivalence agrees with evaluation of the underlying diagram
equivalence at the base vertex. -/
@[simp]
theorem baseEquivalence.app (e : S ≌ T) :
    baseEquivalence e =
      (diagramEquivalence e).app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) := sorry

/-- The forward morphism of the left-endpoint equivalence is the left component of the
forward bundled-cospan morphism. -/
@[simp]
theorem leftEquivalence.hom (e : S ≌ T) :
    (leftEquivalence e).hom = Hom.left e.hom := sorry

/-- The inverse morphism of the left-endpoint equivalence is the left component of the
inverse bundled-cospan morphism. -/
@[simp]
theorem leftEquivalence.inv (e : S ≌ T) :
    (leftEquivalence e).inv = Hom.left e.inv := sorry

/-- The forward morphism of the right-endpoint equivalence is the right component of the
forward bundled-cospan morphism. -/
@[simp]
theorem rightEquivalence.hom (e : S ≌ T) :
    (rightEquivalence e).hom = Hom.right e.hom := sorry

/-- The inverse morphism of the right-endpoint equivalence is the right component of the
inverse bundled-cospan morphism. -/
@[simp]
theorem rightEquivalence.inv (e : S ≌ T) :
    (rightEquivalence e).inv = Hom.right e.inv := sorry

/-- The forward morphism of the common-target equivalence is the base component of the
forward bundled-cospan morphism. -/
@[simp]
theorem baseEquivalence.hom (e : S ≌ T) :
    (baseEquivalence e).hom = Hom.base e.hom := sorry

/-- The inverse morphism of the common-target equivalence is the base component of the
inverse bundled-cospan morphism. -/
@[simp]
theorem baseEquivalence.inv (e : S ≌ T) :
    (baseEquivalence e).inv = Hom.base e.inv := sorry

/- Data and axiom audit (mathlib 4.32):

The three declarations are direct applications of `Pseudofunctor.mapEquivalence` to the
canonical vertex projections. They make no new choices of inverse, unit, counit, or triangle
data. `#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]`, with
`sorryAx` inherited from the generic mapped-equivalence and projection coherence fields. -/

end CategoryTheory.Bicategory.Cospan
