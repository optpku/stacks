/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_12_2_InfinitesimalNeighbourhood

/-!
# Universal property of infinitesimal neighbourhoods of immersions of algebraic spaces

The first-order (resp. `n`th-order) infinitesimal neighbourhood of an immersion
of algebraic spaces is universal among first-order (resp. `n`th-order)
thickenings over the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.InfinitesimalNeighbourhood

/-- Lemma 76.12.2 (1): every first-order thickening over the ambient algebraic
space uniquely factors through the first-order infinitesimal neighbourhood of an
immersion. -/
@[stacks 05ZW]
theorem existsUnique_lift_firstOrder {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (j : T ⟶ T') [IsFirstOrderThickening j]
    (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    Nonempty (Unique (factorizationCommSq i 1 j a b sq).LiftStruct) :=
  sorry

/-- Lemma 76.12.2 (2): for `1 ≤ n`, every `n`th-order thickening over the ambient
algebraic space uniquely factors through the `n`th infinitesimal neighbourhood of
an immersion. -/
@[stacks 05ZW]
theorem existsUnique_lift {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (n : ℕ) (hn : 1 ≤ n) (j : T ⟶ T')
    [IsNthOrderThickening n j] (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    Nonempty (Unique (factorizationCommSq i n j a b sq).LiftStruct) :=
  sorry

/-- A first-order or finite-order thickening square over `X` admits a unique
morphism of thickenings over `X` to the infinitesimal neighbourhood, with
prescribed map on the closed subspace. -/
theorem existsUnique_hom {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (n : ℕ) (hn : 1 ≤ n) (j : T ⟶ T')
    [IsNthOrderThickening n j] (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    ∃! g : Thickening.of j ⟶ Thickening.of (fromSource i n),
      g.left = a ∧ g.right ≫ toAmbient i n = b :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
