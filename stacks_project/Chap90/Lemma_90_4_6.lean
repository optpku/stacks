/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_4_6_Derivation

/-!
# Surjectivity from injectivity of residue-derivation restriction

A morphism in `CompleteLocalAlgCat Λ k` is surjective whenever the induced restriction
map on `Λ`-derivations into the identified residue field `k` is injective.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat
namespace Hom

/-- Lemma 90.4.6: if `f : R ⟶ S` is a morphism in `Ĉ_Λ = CompleteLocalAlgCat Λ k` and the
restriction map `mapDerivation f : Derivation Λ S.carrier k → Derivation Λ R.carrier k` is
injective, then the underlying algebra map of `f` is surjective. -/
@[stacks 06SD]
theorem surjective_of_mapDerivation_injective {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Injective (mapDerivation f)) : Function.Surjective f.hom :=
  sorry

end Hom
end CompleteLocalAlgCat
