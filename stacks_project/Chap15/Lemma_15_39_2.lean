module

public import ReasLib.RingTheory.MvPowerSeries.Parameters
import StacksCheckRecall

/-!
# Lemma 15.39.2

@stack 07NM
-/

@[expose] public section

/- Lemma 15.39.2 (1), tag `07NM`: a regular system of parameters in a finite-variable power
series ring over a field defines a bijective canonical substitution map. -/
@[stacks 07NM "part 1 map"]
#check @MvPowerSeries.regularParameterSubst

@[stacks 07NM "part 1 variables"]
#check @MvPowerSeries.regularParameterSubst_X

@[stacks 07NM "part 1 bijectivity"]
#check @MvPowerSeries.regularParameterSubst_bijective

/- Lemma 15.39.2 (2), tag `07NM`: a partial regular system has at most `n` elements, and the
corresponding quotient is a power series ring in the complementary variables. -/
@[stacks 07NM "part 2 length"]
#check @IsLocalRing.IsPartOfRegularSystemOfParameters.length_le

@[stacks 07NM "part 2 quotient"]
#check @MvPowerSeries.exists_quotientAlgEquiv_of_isPartOfRegularSystemOfParameters

/- Lemma 15.39.2 (3), tag `07NM`: over a Cohen ring, the residue characteristic followed by a
regular parameter family defines a bijective continuous evaluation map. -/
@[stacks 07NM "part 3 residue characteristic"]
#check @MvPowerSeries.cohenResidueCharacteristicParameter

@[stacks 07NM "part 3 map"]
#check @MvPowerSeries.cohenParameterEval

@[stacks 07NM "part 3 variables"]
#check @MvPowerSeries.cohenParameterEval_X

@[stacks 07NM "part 3 bijectivity"]
#check @MvPowerSeries.cohenParameterEval_bijective

/- Lemma 15.39.2 (4), tag `07NM`: if the residue characteristic followed by a partial parameter
family is regular, then its length is at most `n` and quotienting by that family leaves a power
series ring in the complementary variables. -/
@[stacks 07NM "part 4 length"]
#check @MvPowerSeries.cohenPartialParameters_length_le

@[stacks 07NM "part 4 quotient"]
#check @MvPowerSeries.exists_cohenQuotientAlgEquiv_of_isPartOfRegularSystemOfParameters
