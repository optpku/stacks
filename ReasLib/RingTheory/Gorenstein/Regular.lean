module

public import ReasLib.RingTheory.Gorenstein.Ring
public import ReasLib.RingTheory.GlobalDimension.Injective
public import ReasLib.RingTheory.GlobalDimension.RegularLocal

@[expose] public section

universe u

/-- Every regular local commutative ring is Gorenstein. -/
instance IsRegularLocalRing.instIsGorensteinLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsGorensteinLocalRing R := sorry

/-- Every regular commutative ring is Gorenstein. -/
instance IsRegularRing.instIsGorensteinRing
    (R : Type u) [CommRing R] [IsRegularRing R] :
    IsGorensteinRing R := sorry
