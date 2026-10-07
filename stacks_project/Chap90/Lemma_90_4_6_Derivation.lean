module

public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.Lemma_90_4_5_Residue

/-!
# Restriction of residue derivations along morphisms in `Ĉ_Λ`

A morphism `f` in `CompleteLocalAlgCat Λ k` induces a `k`-linear restriction map
`Derivation Λ S.carrier k →ₗ[k] Derivation Λ R.carrier k` by precomposition with the
underlying algebra map of `f`.
-/

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat
namespace Hom

/-- The restriction map `Derivation Λ S.carrier k → Derivation Λ R.carrier k` induced by a
morphism `f` in `CompleteLocalAlgCat Λ k`, given by precomposition with the underlying
algebra map of `f`. -/
def mapDerivation {R S : CompleteLocalAlgCat Λ k} (f : Hom R S) :
    Derivation Λ S.carrier k →ₗ[k] Derivation Λ R.carrier k where
  toFun D :=
    { toLinearMap := D.toLinearMap.comp f.hom.toLinearMap
      map_one_eq_zero' := sorry
      leibniz' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The restriction of a residue derivation along `f` evaluates as precomposition with the
underlying algebra map of `f`. -/
theorem mapDerivation_apply {R S : CompleteLocalAlgCat Λ k} (f : Hom R S)
    (D : Derivation Λ S.carrier k) (x : R.carrier) :
    mapDerivation f D x = D (f.hom x) :=
  sorry

end Hom
end CompleteLocalAlgCat
