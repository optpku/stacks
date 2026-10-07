module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.Lemma_90_4_5_Residue

/-!
# Finite-dimensionality of residue derivations

For an object of the completed base category `Ĉ_Λ`, the space of `Λ`-derivations into the
identified residue field `k` is finite-dimensional over `k`.
-/

@[expose] public section

open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.4.5: for any object `S` of `Ĉ_Λ = CompleteLocalAlgCat Λ k`, the `k`-vector space
`Derivation Λ S.carrier k` of `Λ`-derivations from `S` into the identified residue field `k`
is finite-dimensional. -/
@[stacks 06SC]
instance finiteDimensional_derivation (S : CompleteLocalAlgCat Λ k) :
    FiniteDimensional k (Derivation Λ S.carrier k) := sorry

end CompleteLocalAlgCat
