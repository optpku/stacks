/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_27_3_Omega
public import stacks_project.Chap92.Lemma_92_27_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of an algebraic space over a ring via derived lower shriek

Lemma 92.27.3 identifies `L_{X/Λ}` in `D(𝒪_X)` with
`Lπ_!(Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X)`, recovering the source chain
`L_{X/Λ} = Lπ_!(Li^* Ω_{O/underline{Λ}}) = Lπ_!(i^* Ω_{O/underline{Λ}}) =
Lπ_!(Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X)`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- Lemma 92.27.3. In the situation above there is a canonical isomorphism
`L_{X/Λ} = Lπ_!(Li^* Ω_{O/underline{Λ}}) = Lπ_!(i^* Ω_{O/underline{Λ}}) =
Lπ_!(Ω_{O/underline{Λ}} ⊗_O underline{𝒪}_X)` in `D(𝒪_X)`. The last two equalities
use that `Ω_{O/underline{Λ}}` is a flat `O`-module because each affine vertex is a
polynomial `Λ`-algebra. -/
@[stacks 08VM]
theorem lowerShriek_omega :
    IsIsomorphic (cotangent (toBase X))
      ((lowerShriek Λ X).obj (singleOmegaTensorInverseImage Λ X)) :=
  sorry

/-- The same identification with `L_{𝒪_X / underline{Λ}}`, via Lemma 92.26.4. -/
theorem lowerShriek_omega_constCotangent :
    IsIsomorphic (constCotangent Λ X)
      ((lowerShriek Λ X).obj (singleOmegaTensorInverseImage Λ X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
