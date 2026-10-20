/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cech.Amitsur

/-!
# Cohomology of associated modules on standard sites

This module compares scheme-module cohomology with the cohomology of the
associated additive sheaf on the standard big and small sites.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Scheme cohomology of a quasi-coherent module agrees with cohomology of its
associated additive sheaf on each standard big site. -/
theorem cohomology_isomorphic_big
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (q : ℕ) [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology F q))
      ((Sheaf.functorH (τ.overTopology S) q).obj
        ((SheafOfModules.toSheaf (bigStructureSheaf τ S)).obj (big τ S F))) := sorry

/-- Scheme cohomology of the structure sheaf agrees with cohomology of its
associated additive sheaf on each standard big site. -/
theorem structureSheaf_cohomology_isomorphic_big
    (τ : StandardTopology) (S : Scheme.{u}) (q : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology (SheafOfModules.unit S.ringCatSheaf : S.Modules) q))
      ((Sheaf.functorH (τ.overTopology S) q).obj
        ((SheafOfModules.toSheaf (bigStructureSheaf τ S)).obj
          (big τ S (SheafOfModules.unit S.ringCatSheaf : S.Modules)))) :=
  cohomology_isomorphic_big τ S (SheafOfModules.unit S.ringCatSheaf : S.Modules) q

/-- Scheme cohomology of a quasi-coherent module agrees with cohomology of its
associated additive sheaf on the small Zariski or small étale site. -/
theorem cohomology_isomorphic_small
    (σ : SmallStandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (q : ℕ) [HasSheafify (σ.topology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (σ.topology S) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology F q))
      ((Sheaf.functorH (σ.topology S) q).obj
        ((SheafOfModules.toSheaf (smallStructureSheaf σ S)).obj (small σ S F))) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
