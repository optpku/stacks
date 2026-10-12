/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.KeyFormula
import StacksCheckRecall

@[expose] public section

open CategoryTheory Function Set Topology
open AlgebraicGeometry

noncomputable section

universe u v

/- Lemma 42.27.1 (Key formula): the locally finite sum of the two order-weighted divisors of
the chosen generators equals the boundary of their tame symbols. -/
@[stacks 0AYC] #check (AlgebraicGeometry.CycleGroup.keyFormula :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
      (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
      (ℒ 𝒩 : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.Invertible 𝒩]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
      (t : X.toLocallyRingedSpace.meromorphicSections 𝒩) (hs : s ≠ 0) (ht : t ≠ 0)
      {I : Type v} (Z : I → PrimeDivisor X) (hZ : Injective Z)
      (hlocal : LocallyFinite fun i ↦ ((Z i).support : Set X))
      (hs_generatorAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) →
        ∃ P : Scheme.RegularMeromorphicSectionOrderPresentation ℒ s
          ((isRegularMeromorphicSection_iff_ne_zero ℒ s).2 hs) W,
          P.quotient = 1)
      (ht_generatorAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) →
        ∃ P : Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t
          ((isRegularMeromorphicSection_iff_ne_zero 𝒩 t).2 ht) W,
          P.quotient = 1)
      (Ps : ∀ i, Scheme.RegularMeromorphicSectionOrderPresentation ℒ s
        ((isRegularMeromorphicSection_iff_ne_zero ℒ s).2 hs) (Z i))
      (Pt : ∀ i, Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t
        ((isRegularMeromorphicSection_iff_ne_zero 𝒩 t).2 ht) (Z i)),
    CycleGroup.locallyFiniteSum (p.relativeDimensionFunction δ) (n - 2)
        (fun i ↦ CycleGroup.keyFormulaTerm p δ n hX ℒ 𝒩 (Z i) (Ps i) (Pt i))
        (CycleGroup.keyFormulaTermsLocallyFinite p δ n hX ℒ 𝒩 Z Ps Pt hlocal) =
      @RationalEquivalence.boundary X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - 2) I
        (fun i ↦ (Z i).genericPoint)
        (fun i ↦ PrimeDivisor.relativeDimensionFunction_genericPoint_eq
          p δ n hX (Z i))
        (fun i ↦ @PrimeDivisor.tameSymbolOnPointClosure X
          (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
          (Z i) (Ps i).quotient (Pt i).quotient)
        (PrimeDivisor.pointClosuresLocallyFinite Z hlocal))
