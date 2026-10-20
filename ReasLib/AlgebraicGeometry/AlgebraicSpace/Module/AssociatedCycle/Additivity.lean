module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedCycle

/-!
# Additivity of associated cycles of coherent modules

Associated degree-`k` cycles are additive in short exact sequences of coherent modules
when all three supports have `δ`-dimension at most `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Over a universally catenary quasi-separated algebraic space equipped with a dimension
function, the degree-`k` module cycle on a quasi-separated locally finite-type algebraic space
is additive in a short exact sequence of coherent modules when all three supports have
`δ`-dimension at most `k`. -/
@[stacks 0EEE]
theorem moduleCycle_eq_add_of_shortExact
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (C : ShortComplex X.Modules)
    [C.X₁.IsCoherent] [C.X₂.IsCoherent] [C.X₃.IsCoherent] (hC : C.ShortExact)
    (k : ℤ) (h₁ : moduleSupportDeltaDimension f δ C.X₁ ≤ (k : EInt))
    (h₂ : moduleSupportDeltaDimension f δ C.X₂ ≤ (k : EInt))
    (h₃ : moduleSupportDeltaDimension f δ C.X₃ ≤ (k : EInt)) :
    moduleCycle f δ C.X₂ k h₂ =
      moduleCycle f δ C.X₁ k h₁ + moduleCycle f δ C.X₃ k h₃ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
