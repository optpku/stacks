module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import stacks_project.Chap62.Definition_62_6_1_Specialization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 62.6.16

Base change of relative cycles along a universal homeomorphism inducing
residue-field isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Base change of a relative `r`-cycle along a morphism of locally Noetherian
bases remains a relative `r`-cycle. -/
theorem groupBaseChange_mem {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : group f r) :
    baseChange f g r (α : Family f r) ∈ group (pullback.snd f g) r := sorry

/-- Base change of relative `r`-cycles along `g : S' ⟶ S`. -/
noncomputable def groupBaseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) : group f r →+ group (pullback.snd f g) r :=
  ((baseChange f g r).restrict (group f r)).codRestrict
    (group (pullback.snd f g) r) (groupBaseChange_mem f g r)

/-- The underlying fibrewise family of `groupBaseChange` is family-level base change. -/
theorem groupBaseChange_apply {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : group f r) :
    (groupBaseChange f g r α : Family (pullback.snd f g) r) =
      baseChange f g r (α : Family f r) := sorry

/-- A fibrewise family is a relative `r`-cycle if and only if its base change along a
universal homeomorphism inducing residue-field isomorphisms is a relative `r`-cycle. -/
theorem isRelative_iff_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g] (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    {r : ℕ} {α : Family f r} :
    IsRelative α ↔ IsRelative (baseChange f g r α) := sorry

/-- Lemma 62.6.16: if `g : S' ⟶ S` is a universal homeomorphism of locally
Noetherian schemes inducing residue-field isomorphisms, and if `f : X ⟶ S` is
locally of finite type, then base change along `g` is a bijection
`z(X/S, r) → z(X'/S', r)` where `X' = S' ×_S X`. -/
@[stacks 0H5G]
theorem groupBaseChange_bijective {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g] (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    Function.Bijective (groupBaseChange f g r) := sorry

end AlgebraicGeometry.RelativeCycle

