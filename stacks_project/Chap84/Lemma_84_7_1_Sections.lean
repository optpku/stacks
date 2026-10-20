module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (U : Over X),
    (associatedPresheaf F).obj (op U) =
      Modules.globalSections ((Modules.pullback U.hom).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_map :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    {U V : Over X} (g : V ⟶ U),
    (associatedPresheaf F).map g.op =
      Modules.globalSectionsPullbackComp g.left U.hom F ≫
        eqToHom
          (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
            (Over.w g)))

#check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_isSheaf_fpqc :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    Presheaf.IsSheaf (overFpqcTopology X) (associatedPresheaf F))

#check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_isSheaf_fppf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    Presheaf.IsSheaf (overFppfTopology X) (associatedPresheaf F))

#check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.associatedPresheaf_isSheaf_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent],
    Presheaf.IsSheaf (overEtaleTopology X) (associatedPresheaf F))

end

end
