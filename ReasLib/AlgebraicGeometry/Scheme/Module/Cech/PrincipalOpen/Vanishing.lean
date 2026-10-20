module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.ModuleDerived
open SheafOfModules.ClosedSubset.SupportedDerived

noncomputable section

universe u

namespace AlgebraicGeometry.ClosedSubset

/-- If a closed subset of a scheme is locally the common zero locus of at most `c`
sections, then its local-cohomology sheaves with quasicoherent coefficients vanish in
degrees strictly greater than `c`. -/
@[stacks 0G7N]
theorem localCohomologySheaf_isZero_of_locallyCutOutBy
    (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) (c : ℕ)
    (hT : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ d : ℕ, d ≤ c ∧ ∃ f : Fin d → Γ(X, U),
        (T : Set X) ∩ (U : Set X) = X.zeroLocus (Set.range f) ∩ (U : Set X))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℤ) (hi : (c : ℤ) < i) :
    IsZero
      (cohomologySheaf
        ((coreflector X.toRingedSpace.ringCatSheaf T ⋙
            inclusion X.toRingedSpace.ringCatSheaf T).obj
          ((ModuleCech.moduleToDerived X).obj ℱ)) i) := sorry

end AlgebraicGeometry.ClosedSubset

end
