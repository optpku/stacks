module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.LocalVanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

/- Lemma 20.7.2 (01E3): a positive-degree cohomology class of an `𝒪_X`-module becomes zero on
every member of a suitable cover of the chosen open.  The source-facing ringed-space bridge is
owned by `ModuleCohomology.existsCoverRestrictEqZero`; the generic site theorem is checked as its
proof-level source. -/
@[stacks 01E3 "positive cohomology classes vanish on a cover"]
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.existsCoverRestrictEqZero

#check @CategoryTheory.Sheaf.exists_cover_restrict_eq_zero_of_positive_cohomology_class

end
