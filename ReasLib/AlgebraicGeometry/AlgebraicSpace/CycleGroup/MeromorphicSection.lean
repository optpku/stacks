/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.HenselianPresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ClosedPushforward


/-! # Cycle contributions of meromorphic sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory Opposite PresheafOfModules
open Function Set Topology
open AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace


namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

variable [IsIntegral X]

/-- The restriction of a good structure morphism to a prime divisor remains
quasi-separated. -/
instance instQuasiSeparated_primeDivisor_structure (Z : PrimeDivisor X) :
    QuasiSeparated (Z.ι ≫ f) :=
  sorry

/-- The restriction of a good structure morphism to a prime divisor remains
locally of finite type. -/
instance instLocallyOfFiniteType_primeDivisor_structure (Z : PrimeDivisor X) :
    LocallyOfFiniteType (Z.ι ≫ f) :=
  sorry

/-- Pullback of an invertible module along a prime-divisor immersion remains
invertible. -/
instance instIsInvertibleObject_pullback_primeDivisor (Z : PrimeDivisor X)
    (L : X.Modules) [isInvertibleObject L] :
    isInvertibleObject ((Modules.pullback Z.ι).obj L) :=
  Modules.isInvertibleObject_pullback Z.ι L

/-- Restrict the generator from the same local ratio presentation. -/
noncomputable def restrictToPrimeDivisor (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L] {s : meromorphicSections X L}
    (d : KeyFormulaPresentation.LocalPresentation s Z) :
    meromorphicSections Z.space ((Modules.pullback Z.ι).obj L) :=
  d.restrictedSection

/-- In the common generic-fibre carrier, the restricted section is precisely
that presentation generator's image along its residue map. -/
theorem restrictToPrimeDivisor_genericGerm (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L] {s : meromorphicSections X L}
    (d : KeyFormulaPresentation.LocalPresentation s Z) :
    KeyFormulaPresentation.LocalPresentation.genericRestriction
      (restrictToPrimeDivisor Z d) = d.generatorImage :=
  d.restrictedSection_generic

/-- This specified restricted generator is a regular meromorphic section. -/
theorem restrictToPrimeDivisor_isRegular (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L] {s : meromorphicSections X L}
    (d : KeyFormulaPresentation.LocalPresentation s Z) :
    IsRegularMeromorphicSection Z.space ((Modules.pullback Z.ι).obj L)
      (restrictToPrimeDivisor Z d) :=
  d.restrictedSection_regular

/-- A regular meromorphic section of an invertible module admits a
local trivialization and fraction at a prime divisor. The coordinate choice
uses the actual henselian identification and its canonical residue triangle.
This range certificate is not used to select any section or formula data. -/
theorem localPresentation_nonempty (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    Nonempty (KeyFormulaPresentation.LocalPresentation s Z) :=
  sorry

variable (δ : Points B → ℤ) [IsDimensionFunction δ]

variable (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)

include hX in
/-- The support of a prime divisor has `δ`-dimension `(n - 2) + 1` when
`dim_δ(X) = n`. -/
theorem primeDivisor_deltaDimension (Z : PrimeDivisor X) :
    deltaDimension f δ (ClosedSubspace.irreducibleClosed Z.subspace) =
      n - 2 + 1 :=
  sorry

variable (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]

/-- The contribution of one prime divisor to the key formula: the order of the
henselian ratio of `s` times the pushed-forward divisor of the restricted
generator of `t`, minus the symmetric term. -/
noncomputable def keyFormulaTerm (Z : PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (sData : KeyFormulaPresentation.LocalPresentation s Z)
    (tData : KeyFormulaPresentation.LocalPresentation t Z) :
    Function.locallyFinsupp (Points X) ℤ :=
  let _ := n
  let _ := hX
  @closedImmersionCyclePushforward S Z.space X Z.ι Z.subspace.isClosedImmersion
    (PrimeDivisor.fractionUnitOrder Z sData.fraction •
        meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z tData)
          (restrictToPrimeDivisor_isRegular Z tData) -
      PrimeDivisor.fractionUnitOrder Z tData.fraction •
        meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z sData)
          (restrictToPrimeDivisor_isRegular Z sData))

/-- Unfolding a key-formula contribution displays its two order-weighted
pushed-forward divisor cycles. -/
theorem keyFormulaTerm_def (Z : PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (sData : KeyFormulaPresentation.LocalPresentation s Z)
    (tData : KeyFormulaPresentation.LocalPresentation t Z) :
    keyFormulaTerm f δ n hX L N Z s hs t ht sData tData =
      @closedImmersionCyclePushforward S Z.space X Z.ι Z.subspace.isClosedImmersion
        (PrimeDivisor.fractionUnitOrder Z
            sData.fraction •
            meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z tData)
              (restrictToPrimeDivisor_isRegular Z tData) -
          PrimeDivisor.fractionUnitOrder Z
            tData.fraction •
            meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z sData)
              (restrictToPrimeDivisor_isRegular Z sData)) :=
  sorry

/-- A one-prime key-formula contribution is an `(n-2)`-cycle. -/
theorem keyFormulaTerm_mem_cycleGroup (Z : PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (sData : KeyFormulaPresentation.LocalPresentation s Z)
    (tData : KeyFormulaPresentation.LocalPresentation t Z) :
    keyFormulaTerm f δ n hX L N Z s hs t ht sData tData ∈
      cycleGroup f δ (n - 2) :=
  sorry

/-- The supports of the component terms in the key formula are locally finite
when the chosen prime divisors are locally finite. -/
theorem keyFormulaTermsLocallyFinite {I : Type v} (Z : I → PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (hlocal : LocallyFinite fun i ↦ ((Z i).pointsSet : Set (Points X)))
    (sData : ∀ i, KeyFormulaPresentation.LocalPresentation s (Z i))
    (tData : ∀ i, KeyFormulaPresentation.LocalPresentation t (Z i)) :
    LocallyFinite fun i ↦
      (keyFormulaTerm f δ n hX L N (Z i) s hs t ht (sData i) (tData i)).support :=
  sorry


/-- The tame symbol on a prime divisor, using local Noetherianity of a good
structure morphism. -/
noncomputable def tameSymbolOnSpace_ofGood (Z : PrimeDivisor X)
    (fi gi : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    (RationalFunction Z.space)ˣ :=
  @PrimeDivisor.tameSymbolOnSpace S X
    (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance Z fi gi

/-- The good-structure tame symbol is the prime-divisor tame symbol. -/
theorem tameSymbolOnSpace_ofGood_eq (Z : PrimeDivisor X)
    (fi gi : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    tameSymbolOnSpace_ofGood f Z fi gi =
      @PrimeDivisor.tameSymbolOnSpace S X
        (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance Z fi gi :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
