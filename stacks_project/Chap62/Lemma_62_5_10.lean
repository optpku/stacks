module

public import stacks_project.Chap62.Lemma_62_5_10_Family
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 62.5.10

Base change of families of cycles on fibres along a bijective morphism inducing
residue-field isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FamilyOfCyclesOnFibres

/-- Lemma 62.5.10: if `g : S' ⟶ S` is bijective on points and every residue-field
map `g.residueFieldMap s'` is an isomorphism, and if `f : X ⟶ S` is locally of
finite type, then base change along `g` is a bijection between the groups of
families of `r`-cycles on fibres of `f` and of `pullback.snd f g`. -/
@[stacks 0H4Y]
theorem baseChange_bijective {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    Function.Bijective (baseChange f g r) := sorry

end AlgebraicGeometry.FamilyOfCyclesOnFibres
