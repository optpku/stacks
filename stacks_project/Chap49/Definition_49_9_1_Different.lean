module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped AlgebraicGeometry

noncomputable section

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different :
    {X Y : Scheme.{u}} → {f : Y ⟶ X} →
    [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] →
    [LocallyOfFiniteType f] → [LocallyQuasiFinite f] →
    (W : f.RelativeDualizingSheaf) → (τ : W.module.obj.sections) → Y.IdealSheafData)

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_ideal_eq_annihilator_sections :
    {X Y : Scheme.{u}} → {f : Y ⟶ X} →
    [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] →
    [LocallyOfFiniteType f] → [LocallyQuasiFinite f] →
    (W : f.RelativeDualizingSheaf) → (τ : W.module.obj.sections) →
    (U : Y.affineOpens) →
    (W.different τ).ideal U =
      RingedSite.IdealSheaf.sections
        (Annihilator.subobject
          (cokernel (W.module.obj.unitHomEquiv.symm τ)))
        (op (U : Y.Opens)))
