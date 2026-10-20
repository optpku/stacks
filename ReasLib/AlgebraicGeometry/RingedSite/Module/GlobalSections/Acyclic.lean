module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Underlying
public import ReasLib.CategoryTheory.Sites.Cohomology.Acyclic

/-!
# Acyclic module sheaves and global sections

This leaf transports total acyclicity of the underlying abelian sheaf to the
module global-sections functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleSections

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}]

section Global

variable [HasSheafify X.siteTopology AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf X.siteTopology AddCommGrpCat.{z})]

/-- Stacks 0731 (3): a module sheaf whose underlying abelian sheaf is totally acyclic is
bounded-below right acyclic for module global sections. -/
@[stacks 0731 "(3), module global sections"]
theorem rightAcyclicForGlobalSections
    (F : ModuleCat.{z} X)
    [Sheaf.IsTotallyAcyclic
      ((SheafOfModules.toSheaf.{z} X.structureSheaf).obj F)] :
    Functor.RightAcyclic.Bounded
      (moduleGlobalSectionsAdditiveFunctor.{z} X) F := sorry

end Global

section Object

variable [HasSheafify X.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf X.siteTopology AddCommGrpCat.{z})]

/-- Stacks 0731 (1): a module sheaf whose underlying abelian sheaf is totally acyclic is
bounded-below right acyclic for sections over every object of the site. -/
@[stacks 0731 "(1)"]
theorem rightAcyclicForObject (U : X) (F : ModuleCat.{z} X)
    [Sheaf.IsTotallyAcyclic
      ((SheafOfModules.toSheaf.{z} X.structureSheaf).obj F)] :
    Functor.RightAcyclic.Bounded (Underlying.sections.{z} X U) F := sorry

end Object

end RingedSite.Hom.ModuleSections
