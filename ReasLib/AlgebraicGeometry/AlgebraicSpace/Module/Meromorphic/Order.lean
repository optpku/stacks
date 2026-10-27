/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Henselian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.RegularPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime


/-! # Orders of meromorphic sections along prime divisors -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory PresheafOfModules
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

namespace MeromorphicSection

/-- The order `ord_{Z, L}(s)` of a regular meromorphic section along a prime
divisor, as the length difference of `IsLocalization.sec` of the pulled ratio
`s / s_ξ` in `Q(O_{X,ξ}^h)`. -/
def ord {L : X.Modules} [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (Z : PrimeDivisor X) : ℤ :=
  let A := henselianLocalRing X Z.genericPoint
  let ab := IsLocalization.sec (nonZeroDivisors A) (henselianFraction s hs Z)
  ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ)

/-- If `s / s_ξ = IsLocalization.mk' a ⟨b, hb⟩` with `a` and `b` nonzerodivisors
in `O_{X,ξ}^h`, then the order is the corresponding length difference. -/
theorem ord_spec [IsLocallyNoetherian X] [IsIntegral X]
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : henselianFraction s hs Z =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩) :
    ord s hs Z =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ) := sorry

/-- The order is the difference of principal-quotient lengths in `O_{X,ξ}^h`. -/
theorem ord_eq_length [IsLocallyNoetherian X] [IsIntegral X]
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : henselianFraction s hs Z =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩) :
    ord s hs Z =
      ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {b})).toNat : ℤ) := sorry

end MeromorphicSection

section
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- An explicit presentation of `s / s_ξ` as a ratio of nonzerodivisors in the
henselian local ring at the generic point of a prime divisor. -/
structure RegularMeromorphicSectionOrderPresentation {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (Z : PrimeDivisor X) where
  /-- The numerator of the local presentation. -/
  num : henselianLocalRing X Z.genericPoint
  /-- The denominator of the local presentation. -/
  den : henselianLocalRing X Z.genericPoint
  /-- The numerator is a nonzerodivisor. -/
  num_mem : num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)
  /-- The denominator is a nonzerodivisor. -/
  den_mem : den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)
  /-- The localization class equals `s / s_ξ`. -/
  eq_mk : Localization.mk num ⟨den, den_mem⟩ = MeromorphicSection.henselianFraction s hs Z

namespace RegularMeromorphicSectionOrderPresentation

/-- Build a presentation from a pair of nonzerodivisors whose localization class
equals `s / s_ξ`. -/
def ofMk {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}
    {hs : IsRegularMeromorphicSection X L s}
    (num den : henselianLocalRing X Z.genericPoint)
    (hnum : num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hden : den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (heq : Localization.mk num ⟨den, hden⟩ =
      MeromorphicSection.henselianFraction s hs Z) :
    RegularMeromorphicSectionOrderPresentation s hs Z where
  num := num
  den := den
  num_mem := hnum
  den_mem := hden
  eq_mk := heq

/-- A presentation records two nonzerodivisors whose localization class equals
`s / s_ξ`. -/
theorem spec {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}
    {hs : IsRegularMeromorphicSection X L s}
    (data : RegularMeromorphicSectionOrderPresentation s hs Z) :
    data.num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint) ∧
      data.den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint) ∧
      Localization.mk data.num ⟨data.den, data.den_mem⟩ =
        MeromorphicSection.henselianFraction s hs Z :=
  sorry

/-- The order attached to a presentation, as the length difference of the principal
quotients by the numerator and denominator. -/
def order {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}
    {hs : IsRegularMeromorphicSection X L s}
    (data : RegularMeromorphicSectionOrderPresentation s hs Z) : ℤ :=
  let A := henselianLocalRing X Z.genericPoint
  ((Ring.ord A data.num).toNat : ℤ) - ((Ring.ord A data.den).toNat : ℤ)

/-- The presentation order is the integer length difference of the principal quotients. -/
theorem order_eq_length {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}
    {hs : IsRegularMeromorphicSection X L s}
    (data : RegularMeromorphicSectionOrderPresentation s hs Z) :
    data.order =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) data.num).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) data.den).toNat : ℤ) :=
  sorry

/-- Every regular meromorphic section admits a henselian local presentation along a
prime divisor. -/
theorem nonempty {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    Nonempty (RegularMeromorphicSectionOrderPresentation s hs Z) :=
  sorry

end RegularMeromorphicSectionOrderPresentation

namespace MeromorphicSection

/-- The canonical order agrees with the order of any explicit local presentation. -/
theorem ord_eq_presentation {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}
    {hs : IsRegularMeromorphicSection X L s}
    (data : RegularMeromorphicSectionOrderPresentation s hs Z) :
    ord s hs Z = data.order :=
  sorry

/-- Multiplying `s / s_ξ` by a unit of `O_{X,ξ}^h` does not change the associated
order of vanishing. -/
theorem henselianFraction_unit {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) (u : (henselianLocalRing X Z.genericPoint)ˣ) :
    ord s hs Z =
      let A := henselianLocalRing X Z.genericPoint
      let q := algebraMap A (FractionRing A) (u : A) * henselianFraction s hs Z
      let ab := IsLocalization.sec (nonZeroDivisors A) q
      ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ) :=
  sorry

end MeromorphicSection

end

end AlgebraicGeometry.AlgebraicSpace
