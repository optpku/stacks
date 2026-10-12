/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow

/-!
# Commutativity of first-Chern cap on Chow groups of algebraic spaces

In Situation 82.2.1, on a good algebraic space, intersecting by the first Chern
classes of two invertible modules commutes on Chow groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
namespace FirstChernChow

/-- Lemma 82.21.3: In Situation 82.2.1 let `X / B` be good. Let `L`, `N` be
invertible on `X`. For any `α : Hom.chowGroup f δ (k + 1 + 1)` we have
`c1(L) ∩ c1(N) ∩ α = c1(N) ∩ c1(L) ∩ α` as elements of
`Hom.chowGroup f δ k`, where `c1(-) ∩ -` is `FirstChernChow.cap`. -/
@[stacks 0EQZ]
theorem cap_comm {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (k : ℤ) (α : Hom.chowGroup f δ (k + 1 + 1)) :
    cap f δ L k (cap f δ N (k + 1) α) =
      cap f δ N k (cap f δ L (k + 1) α) :=
  sorry

end FirstChernChow
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
