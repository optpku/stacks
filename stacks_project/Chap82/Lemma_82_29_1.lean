/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.«82_29_1_1_Tensor»

/-!
# Chern classes after tensoring with an invertible sheaf

The identity `c_i(E ⊗ L)` in the Chow cohomology ring `A^*(X)` of a good
algebraic space, as a binomial expansion in `c_*(E)` and `c₁(L)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChernClass
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
open scoped BigOperators MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

/-- Lemma 82.29.1: In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r`, and let `L` be an invertible
`𝒪_X`-module. Then
`c_i(E ⊗ L) = ∑_{j=0}^i Nat.choose (r + j - i) j • c_{i-j}(E) * c₁(L)^j`
in `A^*(X)`. -/
@[stacks 0ES4]
theorem tensor_invertible {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E L : X.Modules) (r i : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [isInvertibleObject L] :
    homogeneous δ f i (chernClass δ f (E ⊗ L) i) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j : ring δ f) *
          homogeneous δ f (i - j : ℕ) (chernClass δ f E (i - j)) *
          ringClass f δ L ^ j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
