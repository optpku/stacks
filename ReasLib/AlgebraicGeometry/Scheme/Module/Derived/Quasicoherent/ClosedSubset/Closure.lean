/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support.WeakSerre
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Shift
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- The property of having quasi-coherent cohomology supported on a closed subset is
triangulated. -/
instance quasiCoherentOnSupportIsTriangulated (X : Scheme.{u})
    (T : TopologicalSpace.Closeds X) :
    (quasiCoherentOnSupport X T).IsTriangulated := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
