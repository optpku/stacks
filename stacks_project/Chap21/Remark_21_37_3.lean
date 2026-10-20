module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.37.3

Let `u : C ⥤ D` be continuous and cocontinuous, and let `R` be a sheaf of rings on `D`.
The source ringed site is formed with the canonical inverse-image ring sheaf.  The module
derived lower-shriek and the abelian derived lower-shriek need not agree after forgetting
module structure; the only unconditional source-level comparison is a natural transformation
from the abelian lower-shriek after forgetting to the module lower-shriek followed by forgetting.

This file is deliberately a recall surface.  The derived functors and their adjunction are
owned by `ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek` and the abelian
inverse-image owner by `ReasLib.CategoryTheory.Sites.Derived.InverseImage`.  Once the square of
derived right adjoints is supplied, its left-adjoint comparison is the generic mate
`CategoryTheory.DerivedBaseChange.mapOfRight`; the chapter does not duplicate that construction.
-/

open CategoryTheory

/- The canonical ringed-site endpoints used by the module derived functors. -/
@[stacks 07AE "(1) inverse-image source ringed site"]
#check @RingedSite.Cocontinuous.moduleInverseImage.source

@[stacks 07AE "(1) inverse-image target ringed site"]
#check @RingedSite.Cocontinuous.moduleInverseImage.target

/- The canonical module inverse-image and lower-shriek functors. -/
@[stacks 07AE "(2) derived module inverse image"]
#check @RingedSite.Cocontinuous.moduleInverseImage.derived

@[stacks 07AE "(2) derived module lower shriek"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived

/- The adjunction supplies the module lower-shriek as the left adjoint of inverse image. -/
@[stacks 07AE "(2) derived module adjunction"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived.adjunction

/- The corresponding abelian derived inverse-image owner and its generic left-adjoint surface. -/
@[stacks 07AE "(3) derived abelian inverse image"]
#check @CategoryTheory.siteAbelianInverseImageDerived

@[stacks 07AE "(3) derived abelian lower shriek"]
#check @CategoryTheory.Functor.leftAdjoint

/- The forgetful functors used in the source diagram are canonical ReasLib constructions. -/
@[stacks 07AE "(4) underlying additive sheaf"]
#check @RingedSite.Hom.underlyingAbelianSheafFunctor

@[stacks 07AE "(4) derived underlying additive sheaf"]
#check @CategoryTheory.Functor.mapDerivedCategory

/- Remark 21.37.3: the comparison from the abelian lower shriek followed by forgetting to the
module lower shriek followed by forgetting is the mate of the corresponding derived
right-adjoint square.  It is not asserted to be an isomorphism. -/
@[stacks 07AE "derived lower-shriek/forgetful comparison"]
#check @CategoryTheory.DerivedBaseChange.mapOfRight

@[stacks 07AE "derived lower-shriek/forgetful comparison owner"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived.underlyingComparison
