module

public import ReasLib.RingTheory.KrullDimension.Relative.Noetherian
import StacksCheckRecall

/-!
# Krull--Akizuki

@stack 00PG
-/

@[expose] public section

/- Lemma 10.119.12 (Krull--Akizuki): every intermediate `R`-subalgebra of a
finite extension of `FractionRing R` is Noetherian when `R` is a Noetherian
domain of Krull dimension `1`. -/
@[stacks 00PG]
#check @Subalgebra.isNoetherianRing_of_ringKrullDim_eq_one

@[stacks 00PG "dimension-at-most-one Krull-Akizuki criterion"]
#check @Subalgebra.isNoetherianRing_of_dimLEOne

end
