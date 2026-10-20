module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper smooth family of relative dimension `n` over a quasi-compact,
quasi-separated base has nonempty fibres. -/
def IsProperSmoothFamily {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) : Prop :=
  CompactSpace S ∧ QuasiSeparatedSpace S ∧ IsProper f ∧ Smooth f ∧
    RelativeDimension f n ∧ ∀ s : S, Nonempty (f.fiber s)

/-- Characterize a proper smooth family by its base, morphism, relative
dimension, and fibre conditions. -/
theorem isProperSmoothFamily_iff {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    IsProperSmoothFamily f n ↔
      CompactSpace S ∧ QuasiSeparatedSpace S ∧ IsProper f ∧ Smooth f ∧
        RelativeDimension f n ∧ ∀ s : S, Nonempty (f.fiber s) := sorry

end AlgebraicGeometry.Scheme.Hom
