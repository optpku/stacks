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

/-!
# Henselian pullback of meromorphic sections

Membership `s ∈ L_ξ` means some global section of `c_ξ^* L` sheafifies to the
identity-étale value of `pullbackMeromorphicSections c_ξ s`, where
`c_ξ = fromHenselization X ξ` and `L_ξ = (Modules.pullback c_ξ).obj L`. The
integer `ord_{Z, L}(s)` is the length difference of a nonzerodivisor
presentation of the ratio `s / s_ξ` in `Q(O_{X,ξ}^h)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open PresheafOfModules
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

/-- The canonical morphism `c_x : Spec(O_{X,x}^h) ⟶ X` is flat. -/
instance instFlat_fromHenselization (x : Points X) : Flat (fromHenselization X x) :=
  sorry

namespace MeromorphicSection

/-- A meromorphic section is regular at a point `x` when some global section of
`L_x = (Modules.pullback (fromHenselization X x)).obj L` sheafifies, as
`LocalizedModule.mk t 1`, to the identity-étale value of
`pullbackMeromorphicSections (fromHenselization X x) L s`. This is the source
membership `s ∈ L_x`. -/
def IsRegularAt {L : X.Modules} (s : meromorphicSections X L) (x : Points X) : Prop :=
  let Y := henselizationSpace X x
  let Lx := (Modules.pullback (fromHenselization X x)).obj L
  let U := op (smallEtaleSite.id (henselizationOver X x))
  ∃ t : (Modules.liftModule Lx).val.obj U,
    (CategoryTheory.toSheafify (smallEtaleTopology Y)
        (meromorphicSectionPresheaf Y Lx).presheaf).app U (LocalizedModule.mk t 1) =
      sections.eval (pullbackMeromorphicSections (fromHenselization X x) L s) U

/-- Regularity at a point is existence of a global section of `c_x^* L` whose
sheafified `LocalizedModule.mk t 1` equals the pulled germ. -/
theorem isRegularAt_iff {L : X.Modules} (s : meromorphicSections X L) (x : Points X) :
    IsRegularAt s x ↔
      let Y := henselizationSpace X x
      let Lx := (Modules.pullback (fromHenselization X x)).obj L
      let U := op (smallEtaleSite.id (henselizationOver X x))
      ∃ t : (Modules.liftModule Lx).val.obj U,
        (CategoryTheory.toSheafify (smallEtaleTopology Y)
            (meromorphicSectionPresheaf Y Lx).presheaf).app U (LocalizedModule.mk t 1) =
          sections.eval (pullbackMeromorphicSections (fromHenselization X x) L s) U :=
  sorry

/-- The henselian local ring `O_{X,x}^h` is ring-equivalent to the identity-étale
value of `𝒪` on `Spec(O_{X,x}^h)`. -/
theorem nonempty_henselianLocalRing_equiv_identitySections (x : Points X) :
    Nonempty
      (henselianLocalRing X x ≃+*
        (commStructureSheafLift (henselizationSpace X x)).obj.obj
          (op (smallEtaleSite.id (henselizationOver X x)))) :=
  sorry

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

/-- The ratio `s / s_ξ` in `Q(O_{X,ξ}^h)`, obtained by choice among fractions
presenting the pulled germ relative to a generator of `c_ξ^* L`. Downstream
users should rely on `henselianFraction_spec` rather than inspect the witness. -/
def henselianFraction {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) : FractionRing (henselianLocalRing X Z.genericPoint) :=
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

end AlgebraicGeometry.AlgebraicSpace
