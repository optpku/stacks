module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.InternalHom

/-!
# Internal Hom of associated étale modules

The internal Hom of quasi-coherent modules on the small étale site of a scheme
is the ringed-site internal Hom of their associated commutative étale modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The internal Hom sheaf of associated étale modules of quasi-coherent
`𝒪_T`-modules, as a module on the small étale site of `T`. -/
noncomputable def etaleInternalHom {T : Scheme.{u}} (F G : T.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (StandardTopology.Small.topology .etale T)
      (StandardSmall.commStructureSheaf .etale T) :=
  InternalHom.obj.{u + 1, u, u + 1}
    (StandardSmall.commStructureSheaf .etale T)
    (StandardSmall.comm .etale T F) (StandardSmall.comm .etale T G)

/-- The étale internal Hom agrees with the monoidal internal Hom of the
associated étale modules. -/
theorem etaleInternalHom_eq {T : Scheme.{u}} (F G : T.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    etaleInternalHom F G =
      (ihom (StandardSmall.comm .etale T F)).obj
        (StandardSmall.comm .etale T G) :=
  sorry

/-- The underlying additive sheaf of the étale internal Hom. -/
noncomputable abbrev etaleInternalHom_toSheaf {T : Scheme.{u}}
    (F G : T.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Sheaf (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf.{u + 1} _).obj (etaleInternalHom F G)

/-- The underlying additive sheaf of étale internal Hom is `toSheaf` of that
module sheaf. -/
theorem etaleInternalHom_toSheaf_eq {T : Scheme.{u}} (F G : T.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    etaleInternalHom_toSheaf F G =
      (SheafOfModules.toSheaf.{u + 1} _).obj (etaleInternalHom F G) :=
  sorry

end AlgebraicGeometry.Scheme.AssociatedModule

