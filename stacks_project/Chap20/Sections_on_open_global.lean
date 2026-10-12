/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

/-!
Sections on an open subset, viewed over the global section ring, are owned by
`ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal`.
The old Chapter 20 names remain thin compatibility abbreviations in that owner; this file is
the source-facing recall block only.
-/

/- Definition 20.14.1.1 / Sections on open global: restriction of scalars and its derived functor. -/
@[stacks 01BH "restriction of section scalars"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.restrictionToGlobal

@[stacks 01BH "sections over global scalars"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.functor

@[stacks 05S9 "cochain-level over-global sections"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.toDerived

@[stacks 05S9 "derived sections over global scalars"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.derived

@[stacks 05S9 "derived sections unit"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.unit

@[stacks 05S9 "derived global sections"]
#check @AlgebraicGeometry.RingedSpace.moduleDerivedGlobalSections

@[stacks 01BH "global-to-open restriction"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.restriction

@[stacks 01BH "nested-open restriction"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.restrictionOfLE

@[stacks 05S9 "derived global-to-open restriction"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.derivedRestriction

@[stacks 05S9 "derived nested-open restriction"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.derivedRestrictionOfLE

@[stacks 05S9 "Mayer-Vietoris restriction map"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.mayerVietorisToBiprod

@[stacks 05S9 "Mayer-Vietoris overlap map"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal.mayerVietorisDifference

/- Compatibility checks for existing Chapter 20 downstream files. -/
#check @moduleSectionsRestrictionToGlobalFunctor
#check @moduleSectionsOverGlobalFunctor
#check @moduleSectionsOverGlobalToDerived
#check @moduleDerivedSectionsOverGlobal
#check @moduleDerivedSectionsOverGlobalUnit
#check @moduleSectionsOverGlobalRestrictionNatTrans
#check @moduleSectionsOverGlobalRestrictionNatTransOfLE
#check @moduleDerivedSectionsOverGlobalRestrictionNatTrans
#check @moduleDerivedSectionsOverGlobalRestrictionNatTransOfLE
#check @moduleDerivedSectionsOverGlobalRestrictionOfLE
#check @moduleDerivedSectionsOverGlobalRestriction
#check @moduleDerivedSectionsOverGlobalMayerVietorisToBiprod
#check @moduleDerivedSectionsOverGlobalMayerVietorisDifference

