module

public import ReasLib.RingTheory.RegularLocalRing.Parameters
import StacksCheckRecall

@[expose] public section

/- Definition 10.60.10 (1): a system of parameters of a Noetherian local ring of dimension `d`
is a sequence `x : Fin d → maximalIdeal R` generating an ideal of definition. -/
@[stacks 00KU]
#check @IsLocalRing.IsSystemOfParameters

/- Definition 10.60.10 (2): if some sequence `x : Fin d → maximalIdeal R` generates the maximal
ideal, then `R` is a regular local ring and `x` is a regular system of parameters. -/
@[stacks 00KU]
#check @IsRegularLocalRing

@[stacks 00KU]
#check @IsLocalRing.IsRegularSystemOfParameters

/- Companion: a Noetherian local ring of dimension `d` is regular iff it admits a regular
system of parameters of length `d`. -/
#check @IsRegularLocalRing.iff_exists_regularSystemOfParameters
