/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flat morphisms locally of finite presentation are universally open

A flat morphism of algebraic spaces that is locally of finite presentation is
universally open.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.6: A flat morphism locally of finite presentation of algebraic
spaces is universally open. -/
@[stacks 042S]
instance UniversallyOpen.of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    UniversallyOpen f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
