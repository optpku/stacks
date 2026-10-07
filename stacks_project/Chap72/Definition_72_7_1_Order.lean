module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap70.Lemma_70_19_3_Henselization
public import stacks_project.Chap71.Definition_71_10_9_Regular
public import stacks_project.Chap71.Lemma_71_10_7
public import stacks_project.Chap71.Lemma_71_10_10
public import stacks_project.Chap72.Definition_72_6_2_Prime
public import stacks_project.Chap72.Lemma_72_6_3

/-!
# Order of vanishing of regular meromorphic sections

On a locally Noetherian integral algebraic space, the order of a regular meromorphic
section of an invertible module along a prime divisor is the length difference of
principal quotients of the henselian local ring at the generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open PresheafOfModules
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

section
variable {X : AlgebraicSpace S} [IsDecent X]

/-- The canonical morphism `c_x : Spec(O_{X,x}^h) ⟶ X` is flat. -/
instance instFlat_fromHenselization (x : Points X) : Flat (fromHenselization X x) :=
  sorry

namespace MeromorphicSection

/-- A fraction `f ∈ Q(O_{X,ξ}^h)` presents the pulled ratio `s / s_ξ` when some
generator `s_ξ` of `c_ξ^* L` satisfies `c_ξ^*(s) = f · s_ξ` after transporting
along a ring equivalence with identity-étale structure sections. -/
def IsRatioOfPulledGerm {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X)
    (f : FractionRing (henselianLocalRing X Z.genericPoint)) : Prop :=
  let ξ := Z.genericPoint
  let Y := henselizationSpace X ξ
  let Lx := (Modules.pullback (fromHenselization X ξ)).obj L
  let U := op (smallEtaleSite.id (henselizationOver X ξ))
  let A := henselianLocalRing X ξ
  let R := (commStructureSheafLift Y).obj.obj U
  ∃ (t : (Modules.liftModule Lx).val.obj U) (a b : A)
    (hb : b ∈ nonZeroDivisors A) (e : A ≃+* R)
    (hreg : e b ∈ (regularStructureSections Y).obj U),
    a ∈ nonZeroDivisors A ∧ Submodule.span R {t} = ⊤ ∧
      f = IsLocalization.mk' (FractionRing A) a ⟨b, hb⟩ ∧
        (CategoryTheory.toSheafify (smallEtaleTopology Y)
            (meromorphicSectionPresheaf Y Lx).presheaf).app U
          (LocalizedModule.mk (e a • t) ⟨e b, hreg⟩) =
          sections.eval (pullbackMeromorphicSections (fromHenselization X ξ) L s) U

/-- Unfolding form of `IsRatioOfPulledGerm`. -/
theorem isRatioOfPulledGerm_iff {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X)
    (f : FractionRing (henselianLocalRing X Z.genericPoint)) :
    IsRatioOfPulledGerm s Z f ↔
      let ξ := Z.genericPoint
      let Y := henselizationSpace X ξ
      let Lx := (Modules.pullback (fromHenselization X ξ)).obj L
      let U := op (smallEtaleSite.id (henselizationOver X ξ))
      let A := henselianLocalRing X ξ
      let R := (commStructureSheafLift Y).obj.obj U
      ∃ (t : (Modules.liftModule Lx).val.obj U) (a b : A)
        (hb : b ∈ nonZeroDivisors A) (e : A ≃+* R)
        (hreg : e b ∈ (regularStructureSections Y).obj U),
        a ∈ nonZeroDivisors A ∧ Submodule.span R {t} = ⊤ ∧
          f = IsLocalization.mk' (FractionRing A) a ⟨b, hb⟩ ∧
            (CategoryTheory.toSheafify (smallEtaleTopology Y)
                (meromorphicSectionPresheaf Y Lx).presheaf).app U
              (LocalizedModule.mk (e a • t) ⟨e b, hreg⟩) =
              sections.eval (pullbackMeromorphicSections (fromHenselization X ξ) L s) U :=
  sorry

end MeromorphicSection

end

section
variable {X : AlgebraicSpace S}
variable [h_locallyNoetherian : IsLocallyNoetherian X] [h_integral : IsIntegral X]

include h_locallyNoetherian h_integral

namespace MeromorphicSection

/-- The ratio `s / s_ξ` in `Q(O_{X,ξ}^h)`, obtained by choice among fractions
presenting the pulled germ relative to a generator of `c_ξ^* L`. Downstream
users should rely on `henselianFraction_spec` rather than inspect the witness. -/
def henselianFraction {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) : FractionRing (henselianLocalRing X Z.genericPoint) :=
  let _ := h_locallyNoetherian
  let _ := hs
  Classical.epsilon fun f : FractionRing (henselianLocalRing X Z.genericPoint) ↦
    IsRatioOfPulledGerm s Z f

/-- The constructed henselian fraction is a ratio presenting the pulled germ. -/
theorem henselianFraction_spec {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    IsRatioOfPulledGerm s Z (henselianFraction s hs Z) :=
  sorry

/-- The order `ord_{Z, L}(s)` of a regular meromorphic section along a prime
divisor, as the length difference of `IsLocalization.sec` of the pulled ratio
`s / s_ξ` in `Q(O_{X,ξ}^h)`. -/
def ord {L : X.Modules} [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (Z : PrimeDivisor X) : ℤ :=
  let _ := h_locallyNoetherian
  let A := henselianLocalRing X Z.genericPoint
  let ab := IsLocalization.sec (nonZeroDivisors A) (henselianFraction s hs Z)
  ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ)

/-- If `s / s_ξ = IsLocalization.mk' a ⟨b, hb⟩` with `a` and `b` nonzerodivisors
in `O_{X,ξ}^h`, then the order is the corresponding length difference. -/
theorem ord_spec {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : henselianFraction s hs Z =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩) :
    ord s hs Z =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ) :=
  sorry

/-- The order is the difference of principal-quotient lengths in `O_{X,ξ}^h`. -/
theorem ord_eq_length {L : X.Modules} [isInvertibleObject L]
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
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {b})).toNat : ℤ) :=
  sorry

end MeromorphicSection

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
