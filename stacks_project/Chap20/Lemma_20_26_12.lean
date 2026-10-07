module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.Resolution
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory HomologicalComplex
open SheafOfModules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Lemma 20.26.12 (06YF): the ringed-space K-flat resolution is owned by the shared
`CochainComplex` API; its termwise-flat bridge is checked alongside the two resolution forms. -/
@[stacks 06YF]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.exists_termwiseEpi_kFlatResolution

#check @AlgebraicGeometry.RingedSpace.CochainComplex.exists_epi_kFlatResolution
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isTermwiseFlat_iff

end AlgebraicGeometry.RingedSpace
