module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.ChangeOfGenerators

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace SheafOfModules.ClosedSubset

noncomputable section

universe u

/- Lemma 36.6.12: replacing a finite family of generators by `Matrix.mulVec A f`,
without changing its scheme-theoretic zero subscheme, multiplies the canonical top
local-cohomology class map by `Matrix.det A`. -/
@[stacks 0G7S] #check
  (ModuleCech.LocalCohomology.classMap_mulVec :
    ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
      (A : Matrix (Fin c) (Fin c) Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (hcut : Scheme.IdealSheafData.ofIdealTop
          (Ideal.span (Set.range (Matrix.mulVec A f))) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range f))),
      (ModuleCech.LocalCohomology.classMap f).app ℱ =
        ModuleCech.LocalCohomology.pullbackSectionMul f (Matrix.det A) ℱ ≫
          ModuleCech.LocalCohomology.transportClassMapApp f (Matrix.mulVec A f)
            (ModuleCech.LocalCohomology.zeroLocus_eq_of_idealSheaf_eq
              f (Matrix.mulVec A f) hcut) ℱ)

end
