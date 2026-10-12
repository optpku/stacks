/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_19_2
public import stacks_project.Chap76.Definition_76_3_1_Radicial

/-!
# Radicial morphisms of algebraic spaces are universally injective

A radicial morphism of algebraic spaces over a scheme is universally injective:
field-valued points of the target lift in at most one way, so the morphism is
injective on field-valued points and hence universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A radicial morphism of algebraic spaces is injective on field-valued points. -/
theorem Radicial.injectiveOnFieldPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Radicial f] : injectiveOnFieldPoints f :=
  sorry

/-- Lemma 76.3.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a radicial morphism of
algebraic spaces over `S`. Then `f` is universally injective. -/
@[stacks 0482]
instance Radicial.universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Radicial f] : UniversallyInjective f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
