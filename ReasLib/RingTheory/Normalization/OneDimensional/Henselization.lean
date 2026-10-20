module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normalization.OneDimensional

/-!
# Henselizations of one-dimensional normalizations

This leaf records the reducedness, Nagata, and dimension-one properties of
henselizations and strict henselizations of reduced Nagata local rings.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Normalization.OneDimensional

namespace Henselization

variable {A : Type u} {Ah : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- A henselization of a reduced one-dimensional Nagata local ring is reduced. -/
@[stacks 0C3V]
theorem isReduced (h_dimension : ringKrullDim A = 1) :
    IsReduced Ah := sorry

/-- A henselization of a reduced one-dimensional Nagata local ring is Nagata. -/
@[stacks 0C3V]
theorem isNagataRing (h_dimension : ringKrullDim A = 1) :
    NagataRing Ah := sorry

/-- A henselization of a reduced one-dimensional Nagata local ring has Krull dimension one. -/
@[stacks 0C3V]
theorem krullDim_eq_one (h_dimension : ringKrullDim A = 1) :
    ringKrullDim Ah = 1 := sorry

end Henselization

namespace StrictHenselization

variable {A : Type u} {Ash : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- A strict henselization of a reduced one-dimensional Nagata local ring is reduced. -/
@[stacks 0C3V]
theorem isReduced (h_dimension : ringKrullDim A = 1) :
    IsReduced Ash := sorry

/-- A strict henselization of a reduced one-dimensional Nagata local ring is Nagata. -/
@[stacks 0C3V]
theorem isNagataRing (h_dimension : ringKrullDim A = 1) :
    NagataRing Ash := sorry

/-- A strict henselization of a reduced one-dimensional Nagata local ring has Krull dimension
one. -/
@[stacks 0C3V]
theorem krullDim_eq_one (h_dimension : ringKrullDim A = 1) :
    ringKrullDim Ash = 1 := sorry

end StrictHenselization

end Normalization.OneDimensional
