module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing

/-!
# Étale cohomology of internal Hom on affine schemes

The internal Hom of associated quasi-coherent étale modules on an affine scheme
has vanishing first cohomology when its source is locally projective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- On an affine scheme, the underlying additive sheaf of the internal Hom of
two associated quasi-coherent étale modules has vanishing first étale
cohomology if the source module is locally projective. -/
theorem etaleInternalHom_firstCohomology_isZero
    {T : Scheme.{u}} [IsAffine T] (F G : T.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] [IsLocallyProjective F]
    [HasSheafify (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1})] :
    IsZero
      ((Sheaf.functorH (StandardTopology.Small.topology .etale T) 1).obj
        ((SheafOfModules.toSheaf.{u + 1} _).obj
          (SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
            (StandardSmall.commStructureSheaf .etale T)
            (StandardSmall.comm .etale T F) (StandardSmall.comm .etale T G)))) :=
  sorry

end AlgebraicGeometry.Scheme.AssociatedModule
