module

public import stacks_project.Chap52.Proposition_52_25_4_Tensor
public import stacks_project.Chap52.Proposition_52_25_4_Polynomial
public import stacks_project.Chap52.Lemma_52_25_3_EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- Proposition 52.25.4: for a coherent triple `F` and an invertible coherent triple `L`, the
integer-indexed Euler characteristic of `F` twisted by the integral tensor powers of `L` is a
numerical polynomial of degree at most the topological Krull dimension of the support of `F`.
The canonical integral powers and their pullback/restriction comparisons are supplied by the
invertible-power API. -/
@[stacks 0F27]
theorem eulerCharacteristic_tensorPower_degreeLE
    (F L : CoherentTriple S) [L.IsInvertible] :
    IsNumericalPolynomialOfDegreeLE
      (fun n : ℤ ↦ (canonicalTwist F L n).eulerCharacteristic)
      (topologicalKrullDim (Scheme.Modules.moduleSupport F.F)) := sorry

end AlgebraicGeometry.CoherentTriple
