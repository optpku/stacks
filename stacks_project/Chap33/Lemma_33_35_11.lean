/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.Multiplication
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

/- Lemma 33.35.11: Let `k` be a field, `n : ℕ`, and `ℱ` a coherent sheaf on
`AlgebraicGeometry.ProjectiveSpace.scheme k n`. If `ℱ` is `m`-regular, then the canonical
multiplication map
`H⁰(ℱ(m)) ⊗[k] H⁰(𝒪(1)) → H⁰(ℱ(m + 1))`
is surjective. -/
@[stacks 08A7] #check
  (AlgebraicGeometry.ProjectiveSpace.twistOneGlobalSectionsTensorMap_surjective_of_isMRegular :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent]
      (m : ℤ),
      AlgebraicGeometry.ProjectiveSpace.IsMRegular k n ℱ m →
        Function.Surjective
          (AlgebraicGeometry.ProjectiveSpace.twistOneGlobalSectionsTensorMap k n ℱ m))
