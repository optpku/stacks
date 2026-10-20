module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Remark 59.23.4 (1): scheme cohomology of the structure sheaf is identified
with additive cohomology on the big fppf site, also denoted H^p_fppf(X, O_X). -/
@[stacks 03P6] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.structureSheaf_cohomology_isomorphic_big .fppf :
    ∀ (X : Scheme.{u}) (p : ℕ)
    [HasSheafify (StandardTopology.fppf.overTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (StandardTopology.fppf.overTopology X) AddCommGrpCat.{u})],
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) p))
      ((Sheaf.functorH (StandardTopology.fppf.overTopology X) p).obj
        ((SheafOfModules.toSheaf
          (Scheme.AssociatedModule.bigStructureSheaf .fppf X)).obj
          (Scheme.AssociatedModule.big .fppf X
            (SheafOfModules.unit X.ringCatSheaf : X.Modules)))))

/- Remark 59.23.4 (2): scheme cohomology of the structure sheaf is identified
with additive cohomology on the big étale site. -/
@[stacks 03P6] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.structureSheaf_cohomology_isomorphic_big .etale :
    ∀ (X : Scheme.{u}) (p : ℕ)
    [HasSheafify (StandardTopology.etale.overTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (StandardTopology.etale.overTopology X) AddCommGrpCat.{u})],
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) p))
      ((Sheaf.functorH (StandardTopology.etale.overTopology X) p).obj
        ((SheafOfModules.toSheaf
          (Scheme.AssociatedModule.bigStructureSheaf .etale X)).obj
          (Scheme.AssociatedModule.big .etale X
            (SheafOfModules.unit X.ringCatSheaf : X.Modules)))))

/- Remark 59.23.4 (3): scheme cohomology of the structure sheaf is identified
with additive cohomology on the big Zariski site. -/
@[stacks 03P6] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.structureSheaf_cohomology_isomorphic_big .zariski :
    ∀ (X : Scheme.{u}) (p : ℕ)
    [HasSheafify (StandardTopology.zariski.overTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (StandardTopology.zariski.overTopology X) AddCommGrpCat.{u})],
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) p))
      ((Sheaf.functorH (StandardTopology.zariski.overTopology X) p).obj
        ((SheafOfModules.toSheaf
          (Scheme.AssociatedModule.bigStructureSheaf .zariski X)).obj
          (Scheme.AssociatedModule.big .zariski X
            (SheafOfModules.unit X.ringCatSheaf : X.Modules)))))

end AlgebraicGeometry.Scheme
