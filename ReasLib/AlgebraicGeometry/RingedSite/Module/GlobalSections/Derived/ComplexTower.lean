module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complex section towers

This leaf owns the objectwise degree, cohomology, and cohomology-sheaf towers attached to a
sequential inverse system of complexes of modules on a ringed site.  The short names under
`RingedSite.Hom.ModuleSections.Underlying` are the reusable interface; the names in
`RingedSite.Hom` below are transparent compatibility aliases for older chapter files.
-/

open CategoryTheory ComplexShape Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections

variable (X : RingedSite.{u, v, w})

namespace Underlying

/- The complex shape is fixed to cochain complexes because all tower consumers use cohomological
  degree.  The coefficient universe `z` remains polymorphic for downstream derived constructions. -/

/-- The degree-`i` additive sections functor of a cochain complex over `U`. -/
@[stacks 08CT "degree sections of a complex"]
abbrev complexDegree (U : X) (i : ℤ) :
    CochainComplex (RingedSite.ModuleCat.{z} X) ℤ ⥤ AddCommGrpCat.{z} :=
  (sections.{z} X U).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex.eval AddCommGrpCat.{z} (up ℤ) i

/-- The degree-`i` section tower obtained by applying `complexDegree` stagewise. -/
@[stacks 08CT "degree section tower of a complex system"]
abbrev complexDegreeTower
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (U : X) (i : ℤ) : SequentialInverseSystem AddCommGrpCat.{z} :=
  F ⋙ complexDegree X U i

/-- The degree-`i` cohomology functor of sections of a cochain complex over `U`. -/
@[stacks 08CT "cohomology of sections of a complex"]
abbrev complexCohomology (U : X) (i : ℤ) :
    CochainComplex (RingedSite.ModuleCat.{z} X) ℤ ⥤ AddCommGrpCat.{z} :=
  (sections.{z} X U).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{z} (up ℤ) i

/-- The degree-`i` cohomology tower obtained from a system of cochain complexes. -/
@[stacks 08CT "cohomology section tower of a complex system"]
abbrev complexCohomologyTower
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (U : X) (i : ℤ) : SequentialInverseSystem AddCommGrpCat.{z} :=
  F ⋙ complexCohomology X U i

/-- The underlying additive cohomology-sheaf functor in degree `i`. -/
@[stacks 08CT "underlying cohomology sheaf of a complex"]
abbrev cohomologySheaf (i : ℤ)
    [CategoryWithHomology (RingedSite.ModuleCat.{z} X)] :
    CochainComplex (RingedSite.ModuleCat.{z} X) ℤ ⥤
      Sheaf X.siteTopology AddCommGrpCat.{z} :=
  HomologicalComplex.homologyFunctor (RingedSite.ModuleCat.{z} X) (up ℤ) i ⋙
    RingedSite.Hom.underlyingAbelianSheafFunctor.{z} X

/-- The underlying additive cohomology-sheaf tower of a system of cochain complexes. -/
@[stacks 08CT "underlying cohomology-sheaf tower"]
abbrev cohomologySheafTower
    (F : SequentialInverseSystem (CochainComplex (RingedSite.ModuleCat.{z} X) ℤ))
    (i : ℤ) [CategoryWithHomology (RingedSite.ModuleCat.{z} X)] :
    SequentialInverseSystem (Sheaf X.siteTopology AddCommGrpCat.{z}) :=
  F ⋙ cohomologySheaf X i

end Underlying
end RingedSite.Hom.ModuleSections

namespace RingedSite.Hom

variable (X : RingedSite.{u, v, w})

/- These aliases are intentionally transparent.  They let existing chapter proofs migrate one
  import at a time while all new code can use the shorter `ModuleSections.Underlying` API. -/

/-- Compatibility alias for `ModuleSections.Underlying.complexDegree`. -/
@[stacks 08CT "compatibility degree sections of a complex"]
abbrev complexSectionDegreeFunctor (U : X) (i : ℤ) :
    CochainComplex (ModuleCat X) ℤ ⥤ AddCommGrpCat.{max u v} :=
  ModuleSections.Underlying.complexDegree.{max u v} X U i

/-- Compatibility alias for `ModuleSections.Underlying.complexDegreeTower`. -/
@[stacks 08CT "compatibility degree section tower"]
abbrev complexSectionDegreeInverseSystem
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (U : X) (i : ℤ) : SequentialInverseSystem AddCommGrpCat.{max u v} :=
  ModuleSections.Underlying.complexDegreeTower.{max u v} X F U i

/-- Compatibility alias for `ModuleSections.Underlying.complexCohomology`. -/
@[stacks 08CT "compatibility cohomology of sections"]
abbrev complexSectionCohomologyFunctor (U : X) (i : ℤ) :
    CochainComplex (ModuleCat X) ℤ ⥤ AddCommGrpCat.{max u v} :=
  ModuleSections.Underlying.complexCohomology.{max u v} X U i

/-- Compatibility alias for `ModuleSections.Underlying.complexCohomologyTower`. -/
@[stacks 08CT "compatibility cohomology section tower"]
abbrev complexSectionCohomologyInverseSystem
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (U : X) (i : ℤ) : SequentialInverseSystem AddCommGrpCat.{max u v} :=
  ModuleSections.Underlying.complexCohomologyTower.{max u v} X F U i

/-- Compatibility alias for `ModuleSections.Underlying.cohomologySheaf`. -/
@[stacks 08CT "compatibility underlying cohomology sheaf"]
abbrev underlyingAbelianCohomologySheafFunctor (i : ℤ)
    [CategoryWithHomology (ModuleCat X)] :
    CochainComplex (ModuleCat X) ℤ ⥤
      Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  ModuleSections.Underlying.cohomologySheaf.{max u v} X i

/-- Compatibility alias for `ModuleSections.Underlying.cohomologySheafTower`. -/
@[stacks 08CT "compatibility underlying cohomology-sheaf tower"]
abbrev underlyingAbelianCohomologySheafInverseSystem
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) [CategoryWithHomology (ModuleCat X)] :
    SequentialInverseSystem (Sheaf X.siteTopology AddCommGrpCat.{max u v}) :=
  ModuleSections.Underlying.cohomologySheafTower.{max u v} X F i

end RingedSite.Hom
