module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Relative.QuasiFinite

@[expose] public section

/-!
# Quasi-finite polynomial localization recall

The reusable owner is `RelativeDimensionAt`. The source hypothesis phrased using the point of the
residue-field fiber is definitionally the canonical statement
`relativeDimensionAt R S q = n`.

@stack 00QE
-/

/- Lemma 10.125.2, tag 00QE: at a relative-dimension-`n` point of a finite-type algebra, some
principal localization is quasi-finite over an `n`-variable polynomial algebra over the base. -/
@[stacks 00QE "quasi-finite polynomial localization from relative dimension"]
#check @RelativeDimensionAt.exists_quasiFinite_polynomial_localizationAway
