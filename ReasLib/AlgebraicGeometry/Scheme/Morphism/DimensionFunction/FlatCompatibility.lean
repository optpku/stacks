module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat morphism is compatible with dimension functions up to the integer shift `c`
when `δ' (g.fiberι s s') = δ s + c` at every generic point `s'` of every fiber over `s`. -/
def IsDimensionFunctionCompatible {S S' : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ) : Prop :=
  ∀ (s : S) (s' : g.fiber s), s' ∈ genericPoints (g.fiber s) →
    δ' (g.fiberι s s') = δ s + c

/-- Compatibility of dimension functions is equivalent to its fiberwise generic-point
formula. -/
theorem isDimensionFunctionCompatible_iff {S S' : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ) :
    g.IsDimensionFunctionCompatible δ δ' c ↔
      ∀ (s : S) (s' : g.fiber s), s' ∈ genericPoints (g.fiber s) →
        δ' (g.fiberι s s') = δ s + c := sorry

/-- A flat morphism is compatible with constant-zero dimension functions with zero shift. -/
theorem isDimensionFunctionCompatible_zero {S S' : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S'] (g : S' ⟶ S) [Flat g]
    [IsDimensionFunction (fun _ : S ↦ (0 : ℤ))]
    [IsDimensionFunction (fun _ : S' ↦ (0 : ℤ))] :
    g.IsDimensionFunctionCompatible
      (fun _ : S ↦ (0 : ℤ)) (fun _ : S' ↦ (0 : ℤ)) 0 := sorry

namespace IsDimensionFunctionCompatible

/-- Compatible dimension functions differ by the chosen shift at a generic point of a
fiber. -/
theorem eq_add {S S' : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    {g : S' ⟶ S} [Flat g] {δ : S → ℤ} [IsDimensionFunction δ]
    {δ' : S' → ℤ} [IsDimensionFunction δ'] {c : ℤ}
    (h : g.IsDimensionFunctionCompatible δ δ' c) (s : S) (s' : g.fiber s)
    (hs' : s' ∈ genericPoints (g.fiber s)) :
    δ' (g.fiberι s s') = δ s + c := sorry

end IsDimensionFunctionCompatible

end AlgebraicGeometry.Scheme.Hom
