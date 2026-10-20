/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/- Proposition 35.9.3 (1): Scheme cohomology of a quasi-coherent module agrees with
cohomology of its associated additive sheaf on each of the five standard big sites. -/
@[stacks 03DW] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.cohomology_isomorphic_big :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
      (q : ℕ) [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})],
      IsIsomorphic
        ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
          (Scheme.Modules.cohomology F q))
        ((Sheaf.functorH (τ.overTopology S) q).obj
          ((SheafOfModules.toSheaf (bigStructureSheaf τ S)).obj (big τ S F))))

/- Proposition 35.9.3 (2): Scheme cohomology of a quasi-coherent module agrees with
cohomology of its associated additive sheaf on the small Zariski or small étale site. -/
@[stacks 03DW] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.cohomology_isomorphic_small :
    ∀ (σ : SmallStandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
      (q : ℕ) [HasSheafify (σ.topology S) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (σ.topology S) AddCommGrpCat.{u})],
      IsIsomorphic
        ((forget₂ (ModuleCat Γ(S, ⊤)) AddCommGrpCat.{u}).obj
          (Scheme.Modules.cohomology F q))
        ((Sheaf.functorH (σ.topology S) q).obj
          ((SheafOfModules.toSheaf (smallStructureSheaf σ S)).obj (small σ S F))))

end AlgebraicGeometry.Scheme.AssociatedModule
