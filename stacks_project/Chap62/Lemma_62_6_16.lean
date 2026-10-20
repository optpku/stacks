module

public import ReasLib.AlgebraicGeometry.RelativeCycle.BaseChange
import StacksCheckRecall

/-!
# Lemma 62.6.16

Base change of relative cycles along a universal homeomorphism inducing
residue-field isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 62.6.16: if `g : S' ⟶ S` is a universal homeomorphism of locally
Noetherian schemes inducing residue-field isomorphisms, and if `f : X ⟶ S` is
locally of finite type, then base change along `g` is a bijection
`z(X/S, r) → z(X'/S', r)` where `X' = S' ×_S X`. -/
@[stacks 0H5G] #check
  (AlgebraicGeometry.RelativeCycle.groupBaseChange_bijective :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
      [AlgebraicGeometry.UniversalHomeomorphism g]
      (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ),
      Function.Bijective (AlgebraicGeometry.RelativeCycle.groupBaseChange f g r))
