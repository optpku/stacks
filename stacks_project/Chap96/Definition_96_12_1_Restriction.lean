module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.SmallEtale

@[expose] public section

universe u

#check (AlgebraicGeometry.GroupoidsOver.restrictToSmallEtale :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S}
    (F : PresheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj)
    (x : X.total),
    CategoryTheory.Presheaf.IsSheaf X.etaleTopology F.presheaf →
      SheafOfModules.{u} (AlgebraicGeometry.Scheme.AssociatedModule.smallStructureSheaf
        .etale (X.p.obj x).left))
