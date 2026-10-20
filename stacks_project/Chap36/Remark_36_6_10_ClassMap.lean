/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

#check (ModuleCech.LocalCohomology.classMap :
  ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)),
    ModuleCech.LocalCohomology.pullbackFunctor f ⟶
      ModuleCech.LocalCohomology.cohomologyFunctor f)

end
