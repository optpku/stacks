/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Envelope
public import stacks_project.Chap62.Lemma_62_6_6_Family
import StacksCheckRecall

/-!
# Hilbert cycle classes after a proper completely decomposed base change
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.9: if `f : X ⟶ S` is of finite type, `S` is Noetherian, `r ≥ 0`,
and `α` is a relative `r`-cycle on `X / S`, then there exists a proper completely
decomposed morphism `g : S' ⟶ S` in the sense of `Scheme.Hom.CompletelyDecomposed`
(More on Morphisms, Definition 37.78.1) such that the base change `g^* α` lies in
the image of the Hilbert cycle-class homomorphism `cycleClassHom`
(62.6.8.1). -/
@[stacks 0H59]
#check (AlgebraicGeometry.RelativeCycle.exists_proper_completelyDecomposed_mem_range_cycleClassHom :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [f.FiniteType] (r : ℕ)
    {α : Family f r} (hα : IsRelative α),
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsProper g ∧ Scheme.Hom.CompletelyDecomposed g ∧
        ∃ σ : FreeAbelianGroup (Hilb (pullback.snd f g) r),
          cycleClassHom (pullback.snd f g) r σ = baseChange f g r α)

/- After a proper completely decomposed base change, equivalently an envelope,
a relative `r`-cycle lies in the range of `cycleClassHom`. -/
#check (AlgebraicGeometry.RelativeCycle.exists_isEnvelope_mem_range_cycleClassHom :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [f.FiniteType] (r : ℕ)
    {α : Family f r} (hα : IsRelative α),
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsEnvelope g ∧
        baseChange f g r α ∈ Set.range (cycleClassHom (pullback.snd f g) r))

end AlgebraicGeometry.RelativeCycle
