/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.RingDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- A locally Noetherian scheme carrying a dualizing complex is universally catenary. -/
theorem universallyCatenary
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω) :
    UniversallyCatenary X := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
