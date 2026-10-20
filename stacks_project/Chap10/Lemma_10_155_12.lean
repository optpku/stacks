module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Comparison
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime
import StacksCheckRecall

@[expose] public section

/-!
# At-prime base change of strict henselizations

Lemma 10.155.12 is a recall of the reusable strict-henselization comparison
and base-change APIs.  A compatible map of residue fields determines only a
proposition-valued nonemptiness and uniqueness result for comparison maps; it
does not select comparison data.  The tensor-localization theorem then takes
that explicit local comparison as input; it does not require the compatible
residue-field map to be bijective.

@stack 08HV
-/

/- Lemma 10.155.12, tag `08HV`: the source's commutative diagram is represented
by a residue-field map `φ` together with
`IsLocalRing.ResidueField.Compatible`.  The shared bridge gives the unique
local comparison with induced map `φ`; the existing at-prime local-target API
then exposes the tensor prime, its contraction to `q` and the maximal ideal of
the left strict henselization.  No bijectivity of `φ` is assumed here; the
bijective tensor criterion belongs to the separate 0C2Z owner. -/
@[stacks 08HV]
#check @AlgHom.Local.ResidueCompatible
#check @IsStrictHenselizationOf.Comparison.nonempty_ofResidueMap
#check @IsStrictHenselizationOf.Comparison.subsingleton_ofResidueMap
#check @IsStrictHenselizationOf.Comparison.existsUnique_ofResidueMap
#check @Localization.AtPrime.LocalTarget.tensorMap
#check @Localization.AtPrime.LocalTarget.tensorPrime
#check @Localization.AtPrime.LocalTarget.localizedAlgebra
#check @Localization.AtPrime.LocalTarget.tensorPrime_comap_includeLeft
#check @Localization.AtPrime.LocalTarget.tensorPrime_comap_includeRight
#check @Localization.AtPrime.LocalTarget.localizedMap_isLocalHom
#check @IsStrictHenselizationOf.BaseChange.AtPrime.Tensor.isStrictHenselizationOf
#check @IsStrictHenselizationOf.BaseChange.AtPrime.Tensor.isStrict_of_bijectiveComparison
