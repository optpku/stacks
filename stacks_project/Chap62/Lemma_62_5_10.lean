/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.BaseChange
import StacksCheckRecall

/-!
# Lemma 62.5.10

Base change of families of cycles on fibres along a bijective morphism inducing
residue-field isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 62.5.10: if `g : S' ⟶ S` is bijective on points and every residue-field
map `g.residueFieldMap s'` is an isomorphism, and if `f : X ⟶ S` is locally of
finite type, then base change along `g` is a bijection between the groups of
families of `r`-cycles on fibres of `f` and of `pullback.snd f g`. -/
@[stacks 0H4Y] #check
  (AlgebraicGeometry.FamilyOfCyclesOnFibres.baseChange_bijective :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
      (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ),
      Function.Bijective (AlgebraicGeometry.FamilyOfCyclesOnFibres.baseChange f g r))
