module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Leray.Degeneration
import StacksCheckRecall

@[expose] public section

/-!
# Degeneration of the Leray spectral sequence

The chapter statements are the opens-ringed-site projections of the reusable single-row and
single-column Grothendieck degeneration API.  Global cohomology and higher direct images retain
their independent owners, so no local Leray package or duplicated proof is exposed here.
-/

/- Lemma 20.13.6 (1): vanishing positive higher direct images identifies source global
cohomology with global cohomology of the ordinary direct image. -/
@[stacks 01F4]
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.Degeneration.row

/- Lemma 20.13.6 (2): vanishing positive target cohomology identifies source global cohomology
with degree-zero cohomology of each higher direct image. -/
@[stacks 01F4]
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.Degeneration.column

/- The canonical hypothesis for part (1) is a single right-derived vanishing proposition. -/
#check @AlgebraicGeometry.RingedSpace.ModuleLeray.Degeneration.rowOfVanishes
#check @AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.vanishesAboveZero_iff

/- The ringed-space owner specializes the general ringed-site degeneration criteria. -/
#check @RingedSite.Hom.Leray.Degeneration.row
#check @RingedSite.Hom.Leray.Degeneration.column

/- The conclusion is written through the reusable underlying-sheaf global-cohomology owner. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying.globalCohomology
