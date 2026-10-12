/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Comparison
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Quasi-finite base change of strict henselizations

@stack 05WR

Lemma 10.156.3 is recalled through the explicit-comparison API.  A compatible
residue-field map determines a propositionally unique local comparison, while
the source comparison is covered by a reusable theorem for every supplied
local comparison under the quasi-finite hypotheses.  No canonical map is
selected as public data.
-/

/- Lemma 10.156.3, tag `05WR`: a compatible map of residue fields lifts to a
propositionally unique local comparison between strict henselizations of
`Localization.AtPrime p` and `Localization.AtPrime q`; when `R → S` is
finite type and quasi-finite at `q`, the target is identified with a tensor
localization.  The source comparison is finite with finite purely
inseparable residue-field extension, and the library API generalizes these
conclusions to every such explicit local comparison. -/
#check @IsStrictHenselizationOf.Comparison.nonempty_ofResidueMap
#check @IsStrictHenselizationOf.Comparison.subsingleton_ofResidueMap
@[stacks 05WR "localized strict-henselization identification"]
#check @IsStrictHenselizationOf.BaseChange.AtPrime.Tensor.isStrictHenselizationOf
@[stacks 05WR "explicit-comparison consequence: finite"]
#check @IsStrictHenselizationOf.BaseChange.AtPrime.QuasiFiniteAt.comparison_finite
@[stacks 05WR "explicit-comparison consequence: purely inseparable residue map"]
#check @IsStrictHenselizationOf.BaseChange.AtPrime.QuasiFiniteAt.residueFieldMap_isPurelyInseparable
@[stacks 05WR "explicit-comparison consequence: finite purely inseparable residue map"]
#check @IsStrictHenselizationOf.BaseChange.AtPrime.QuasiFiniteAt.residueFieldMap_finitePurelyInseparable
