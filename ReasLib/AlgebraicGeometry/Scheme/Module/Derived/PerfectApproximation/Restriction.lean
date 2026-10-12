/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PerfectApproximation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HasPerfectApproximation

/-- A perfect approximation on an open subscheme extends to the ambient scheme when the
closed support lies in the open and all relevant cohomology sheaves have that support. -/
theorem of_restrict {X : Scheme.{u}} (T : Closeds X) (U : X.Opens)
    (hTU : (T : Set X) ⊆ (U : Set X))
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ)
    (hU : @HasPerfectApproximation U.toScheme
      (T.preimage continuous_subtype_val)
      ((AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullback U.ι).obj E) m)
    (hE : ∀ i : ℤ, m ≤ i →
      RingedSpace.moduleSupportedOn (T : Set X)
        (RingedSpace.ModuleDerived.cohomologySheaf E.obj i)) :
    HasPerfectApproximation T E m := sorry

end AlgebraicGeometry.Scheme.HasPerfectApproximation
