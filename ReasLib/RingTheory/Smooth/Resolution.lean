module

public import ReasLib.RingTheory.Smooth.Factorization.BaseControl
public import ReasLib.RingTheory.Smooth.Resolution.AtPrime
public import ReasLib.RingTheory.Smooth.Resolution.GeometricallyRegular
public import ReasLib.RingTheory.Smooth.Resolution.Ideal
public import ReasLib.RingTheory.Smooth.Resolution.Localization
public import ReasLib.RingTheory.Smooth.Resolution.OverField
public import ReasLib.RingTheory.Smooth.Resolution.Quotient
public import ReasLib.RingTheory.Smooth.Resolution.PrincipalAnnihilator

@[expose] public section

/-!
# Resolution of algebra maps at primes

This is the stable aggregate import. Clients may import the `Ideal`, `AtPrime`,
`GeometricallyRegular`, `Quotient`, `Localization`, `OverField`, or
`PrincipalAnnihilator` leaf when they only need one layer of the resolution API.
-/
