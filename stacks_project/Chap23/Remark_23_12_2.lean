module

public import ReasLib.RingTheory.Sequence.Koszul.Tate.Pro
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Powered Koszul--Tate pro-systems

The reusable owner records the source's strictly increasing exact exponents, the finite-cell Tate
approximations between consecutive selected Koszul stages, and both rows of comparison maps.  It
constructs the middle transition as the prescribed composite, exposes the commuting three-row
diagram as natural transformations, and realizes the resulting representative inverse in `Pro`.
-/

/- Remark 23.12.2 (Tag 0GZ5): over a Noetherian ring the canonical powered Koszul divided-power
system admits a coherent Koszul--Tate tower starting at exponent `1`. -/
universe u x

section Existence

variable {R : Type u} [CommRing R]
variable {ι : Type u} [Finite ι]
variable (f : ι → R) [IsNoetherianRing R]

@[stacks 0GZ5 "existence of a canonical powered Koszul--Tate tower"]
#check (KoszulComplex.Tate.Tower.nonempty_canonical f :
  Nonempty (KoszulComplex.Tate.Tower.{u, x} (KoszulComplex.DP.system f)))

end Existence

#check @KoszulComplex.DP.system
#check @KoszulComplex.DP.tower
#check @KoszulComplex.Tate.Tower
#check @KoszulComplex.Tate.Tower.exponent_zero
#check @KoszulComplex.Tate.Tower.exponent_strictMono
#check @KoszulComplex.Tate.Tower.fromKoszul
#check @KoszulComplex.Tate.Tower.toKoszul
#check @KoszulComplex.Tate.Tower.fromKoszul_toKoszul
#check @KoszulComplex.Tate.Tower.step
#check @KoszulComplex.Tate.Tower.system
#check @KoszulComplex.Tate.Tower.system_stepMap
#check @KoszulComplex.Tate.Tower.top_commutes
#check @KoszulComplex.Tate.Tower.bottom_commutes
#check @KoszulComplex.Tate.Tower.fromKoszulNatTrans
#check @KoszulComplex.Tate.Tower.toKoszulNatTrans
#check @KoszulComplex.Tate.Tower.factorization
#check @KoszulComplex.Tate.Tower.comparison
#check @KoszulComplex.Tate.Tower.comparisonInverse
#check @KoszulComplex.Tate.Tower.comparison_hasRepresentativeInverse

/- Remark 23.12.2 (Tag 0GZ5): the powered Koszul and Tate inverse systems are isomorphic in the
pro-category of divided-power chain DGAs. -/
section Comparison

variable {R : Type u} [CommRing R]
variable {ι : Type u} [Finite ι]
variable {f : ι → R}
variable {K : KoszulComplex.DP.System f}
variable (T : KoszulComplex.Tate.Tower K)

@[stacks 0GZ5 "Koszul--Tate pro-isomorphism"]
#check (KoszulComplex.Tate.Tower.comparison_isIso T :
  IsIso T.comparison.toHom)

end Comparison
#check @KoszulComplex.Tate.Tower.comparisonIsIso

#check @KoszulComplex.DP.tower_comp_forget
#check @KoszulComplex.Tate.Approximation.fromKoszul_augmentation
#check @KoszulComplex.Tate.Approximation.toKoszul_commutesOnH0
