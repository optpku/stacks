/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.QuasiCompact

/-!
# Universally closed relative projective spectra

This file formulates affine-chart integrality over degree zero and the resulting universal
closedness of a relative projective-spectrum morphism.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} {p : X ⟶ S}

namespace RelativeProjPresentation

/-- A relative projective-spectrum presentation is integral over degree zero when the canonical
map from the base ring to the degree-zero ring is integral on every affine chart. -/
def IntegralDegreeZeroAlgebra (P : RelativeProjPresentation p) : Prop :=
  ∀ s : S, (P.affineChart s).affineAlgebra.baseToZero.hom.IsIntegral

namespace IntegralDegreeZeroAlgebra

/-- A relative projective-spectrum morphism is universally closed when its affine models are
integral over degree zero and finite type over degree zero. -/
theorem universallyClosed {P : RelativeProjPresentation p}
    (hIntegral : P.IntegralDegreeZeroAlgebra)
    (hFiniteType : P.FiniteTypeAsDegreeZeroAlgebra) :
    UniversallyClosed p := sorry

end IntegralDegreeZeroAlgebra

end RelativeProjPresentation

end AlgebraicGeometry.Scheme.Hom
