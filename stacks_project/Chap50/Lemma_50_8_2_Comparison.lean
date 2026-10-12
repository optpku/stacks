/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.Scheme.Hom
open DerivedCategory.DerivedTensor RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

/- Compatibility check for the localized de Rham comparison. -/
#check derivedComparison

/- Compatibility check for the localized comparison specification. -/
#check derivedComparison_eq

/- Compatibility check for the localized comparison isomorphism theorem. -/
#check derivedComparison_isIso

/- Compatibility check for the global de Rham comparison. -/
#check globalComparison

/- Compatibility check for the global comparison specification. -/
#check globalComparison_eq

/- Compatibility check for the affine de Rham comparison. -/
#check affineComparison

/- Compatibility check for the affine comparison specification. -/
#check affineComparison_eq

/- Compatibility check for the affine comparison isomorphism theorem. -/
#check affineComparison_isIso

end AlgebraicGeometry.Scheme.DeRham.Kunneth
