/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.HCovering

/-!
# Descent of relative cycles along h coverings

A family of `r`-cycles on fibres of `X / S` is a relative cycle if and only if
every base change along an h covering of `S` is a relative cycle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.3: if `S` is locally Noetherian and `f : X ⟶ S` is locally of
finite type, then a family `α` of `r`-cycles on fibres of `X / S` is a
relative `r`-cycle if and only if every base change of `α` along an h
covering `{g_i : S_i ⟶ S}` is a relative `r`-cycle. -/
@[stacks 0H52] #check (AlgebraicGeometry.RelativeCycle.isRelative_iff_hCovering_baseChange :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family],
    IsRelative α ↔
      ∀ i, IsRelative (FamilyOfCyclesOnFibres.baseChange f (family i).hom r α))

end AlgebraicGeometry.RelativeCycle
