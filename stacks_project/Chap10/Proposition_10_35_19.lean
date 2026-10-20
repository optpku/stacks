module

public import ReasLib.RingTheory.Spectrum.Prime.Jacobson.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.35.19

@stack 00GB

The canonical owners are `isJacobsonRing_of_finiteType` and the ReasLib finite-type
closed-point API in `PrimeSpectrum`.
-/

/- Proposition 10.35.19 (1): a finite type algebra over a Jacobson ring is Jacobson. -/
@[stacks 00GB "(1)"]
#check @isJacobsonRing_of_finiteType

@[stacks 00GB "(2)"]
#check @PrimeSpectrum.comap_mapsTo_closedPoints

@[stacks 00GB "(3)"]
#check @PrimeSpectrum.moduleFinite_residueField_of_isMaximal

@[stacks 00GB "closed-point map"]
#check @PrimeSpectrum.comapClosedPoints

@[stacks 00GB "ring-hom closed-point form"]
#check @PrimeSpectrum.comap_mapsTo_closedPoints_of_finiteType

@[stacks 00GB "closed-point map value"]
#check @PrimeSpectrum.val_comapClosedPoints

@[stacks 00GB "closed-point contraction"]
#check @PrimeSpectrum.comap_asIdeal_isMaximal_of_isMaximal

@[stacks 00GB "closed-point residue-field form"]
#check @PrimeSpectrum.moduleFinite_residueField_of_mem_closedPoints
