/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Derivation

/-!
# Finite-dimensionality of residue derivations

For an object of the completed base category `Ĉ_Λ`, the space of `Λ`-derivations into the
identified residue field `k` is finite-dimensional over `k`.
-/

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.4.5: for any object `S` of `Ĉ_Λ = CompleteLocalAlgCat Λ k`, the `k`-vector space
`Derivation Λ S.carrier k` of `Λ`-derivations from `S` into the identified residue field `k`
is finite-dimensional. -/
@[stacks 06SC] #check (CompleteLocalAlgCat.finiteDimensional_derivation :
  ∀ S : CompleteLocalAlgCat Λ k, FiniteDimensional k (Derivation Λ S.carrier k))
