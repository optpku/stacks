module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RelativeCycle.Hilbert
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Hilbert cycle classes after envelope base change
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- A relative cycle for a finite-type morphism to a Noetherian scheme becomes
a Hilbert cycle class after a proper, completely decomposed base change. -/
theorem exists_proper_completelyDecomposed_mem_range_cycleClassHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [f.FiniteType] (r : ℕ)
    {α : f.FiberCycleFamily r} (hα : IsRelative α) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsProper g ∧ Scheme.Hom.CompletelyDecomposed g ∧
        ∃ σ : FreeAbelianGroup (Hilb (pullback.snd f g) r),
          cycleClassHom (pullback.snd f g) r σ =
            FamilyOfCyclesOnFibres.baseChange f g r α := sorry

/-- A relative cycle for a finite-type morphism to a Noetherian scheme lies
in the range of the Hilbert cycle-class homomorphism after an envelope base change. -/
theorem exists_isEnvelope_mem_range_cycleClassHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [f.FiniteType] (r : ℕ)
    {α : f.FiberCycleFamily r} (hα : IsRelative α) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S),
      IsEnvelope g ∧
        FamilyOfCyclesOnFibres.baseChange f g r α ∈
          Set.range (cycleClassHom (pullback.snd f g) r) := sorry

end AlgebraicGeometry.RelativeCycle
