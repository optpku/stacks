module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap62.«62_6_8_1_CycleClass»

/-!
# Hilbert cycle classes after a proper completely decomposed base change
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.9: if `f : X ⟶ S` is of finite type, `S` is Noetherian, `r ≥ 0`,
and `α` is a relative `r`-cycle on `X / S`, then there exists a proper completely
decomposed morphism `g : S' ⟶ S` in the sense of `Scheme.Hom.CompletelyDecomposed`
(More on Morphisms, Definition 37.78.1) such that the base change `g^* α` lies in
the image of the Hilbert cycle-class homomorphism `cycleClassHom`
(62.6.8.1). -/
@[stacks 0H59]
theorem exists_proper_completelyDecomposed_mem_range_cycleClassHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [f.FiniteType] (r : ℕ)
    {α : Family f r} (hα : IsRelative α) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsProper g ∧ Scheme.Hom.CompletelyDecomposed g ∧
        ∃ σ : FreeAbelianGroup (Hilb (pullback.snd f g) r),
          cycleClassHom (pullback.snd f g) r σ = baseChange f g r α :=
  sorry

/-- After a proper completely decomposed base change, equivalently an envelope,
a relative `r`-cycle lies in the range of `cycleClassHom`. -/
theorem exists_isEnvelope_mem_range_cycleClassHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [f.FiniteType] (r : ℕ)
    {α : Family f r} (hα : IsRelative α) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsEnvelope g ∧
        baseChange f g r α ∈ Set.range (cycleClassHom (pullback.snd f g) r) :=
  sorry

end AlgebraicGeometry.RelativeCycle
