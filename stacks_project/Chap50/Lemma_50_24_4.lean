module

public import stacks_project.Chap50.Situation_50_24_1
public import stacks_project.Chap50.Lemma_50_24_4_Differential
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- Lemma 50.24.4: in Situation 50.24.1, the map on degree-`n` higher direct images
induced by `d : Ω^(n - 1)_{X/S} ⟶ Ω^n_{X/S}` is zero. -/
@[stacks 0G8J]
theorem topHigherDirectImageDifferential_eq_zero {X S : Scheme.{u}}
    (f : X ⟶ S) (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n]
    (h_nonempty : ∀ s : S, Nonempty (f.fiber s)) :
    topHigherDirectImageDifferential f n = 0 := sorry

end AlgebraicGeometry.Scheme.DeRham
