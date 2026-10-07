module

public import ReasLib.AlgebraicGeometry.ChowGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime.PointClosure

/-!
# The key formula for divisors of meromorphic sections

This file defines the contribution of a prime divisor to the key formula and states the
equality between the resulting locally finite cycle and the boundary of the tame symbols.
-/

@[expose] public section

open CategoryTheory Function Set Topology
open AlgebraicGeometry.LocallyRingedSpace
open AlgebraicGeometry.Scheme.Modules.MeromorphicSection

noncomputable section

universe u v

namespace AlgebraicGeometry.CycleGroup

/-- The contribution of one prime divisor to the key formula: the order of the first section
times the pushed-forward divisor of the second chosen generator, minus the symmetric term. -/
noncomputable def keyFormulaTerm
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
    (ℒ 𝒩 : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.Invertible 𝒩]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {t : X.toLocallyRingedSpace.meromorphicSections 𝒩}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {ht : X.toLocallyRingedSpace.IsRegularMeromorphicSection 𝒩 t}
    (Z : PrimeDivisor X)
    (Ps : Scheme.RegularMeromorphicSectionOrderPresentation ℒ s hs Z)
    (Pt : Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t ht Z) :
    CycleGroup X (p.relativeDimensionFunction δ) (n - 2) :=
  (@Scheme.RegularMeromorphicSectionOrderPresentation.order X
      (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
      ℒ inferInstance s Z hs Ps) •
      mapHom (Scheme.PointClosure.ι Z.genericPoint)
        ((Scheme.PointClosure.ι Z.genericPoint ≫ p).relativeDimensionFunction δ)
        (p.relativeDimensionFunction δ) (n - 2)
        (@relativeDivisorCycle S (Scheme.PointClosure.scheme Z.genericPoint)
          (Scheme.PointClosure.ι Z.genericPoint ≫ p) inferInstance
          (AlgebraicGeometry.locallyOfFiniteType_comp
            (Scheme.PointClosure.ι Z.genericPoint) p
            (hf := inferInstanceAs (LocallyOfFiniteType
              (Scheme.PointClosure.reducedStructure Z.genericPoint).ι))) δ inferInstance
          inferInstance ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι Z.genericPoint)).obj 𝒩)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι Z.genericPoint) inferInstance)
          (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure X
            (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
            𝒩 inferInstance t ht Z Pt)
          (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure_ne_zero X
            (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
            𝒩 inferInstance t ht Z Pt)
          (n - 2)
          (PrimeDivisor.pointClosure_relativeDimension p δ n hX Z)) -
    (@Scheme.RegularMeromorphicSectionOrderPresentation.order X
      (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
      𝒩 inferInstance t Z ht Pt) •
      mapHom (Scheme.PointClosure.ι Z.genericPoint)
        ((Scheme.PointClosure.ι Z.genericPoint ≫ p).relativeDimensionFunction δ)
        (p.relativeDimensionFunction δ) (n - 2)
        (@relativeDivisorCycle S (Scheme.PointClosure.scheme Z.genericPoint)
          (Scheme.PointClosure.ι Z.genericPoint ≫ p) inferInstance
          (AlgebraicGeometry.locallyOfFiniteType_comp
            (Scheme.PointClosure.ι Z.genericPoint) p
            (hf := inferInstanceAs (LocallyOfFiniteType
              (Scheme.PointClosure.reducedStructure Z.genericPoint).ι))) δ inferInstance
          inferInstance ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι Z.genericPoint) inferInstance)
          (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure X
            (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
            ℒ inferInstance s hs Z Ps)
          (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure_ne_zero X
            (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
            ℒ inferInstance s hs Z Ps)
          (n - 2)
          (PrimeDivisor.pointClosure_relativeDimension p δ n hX Z))

/-- Unfolding a key-formula contribution displays its two order-weighted pushed-forward
divisor cycles. -/
theorem keyFormulaTerm_def
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
    (ℒ 𝒩 : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.Invertible 𝒩]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {t : X.toLocallyRingedSpace.meromorphicSections 𝒩}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {ht : X.toLocallyRingedSpace.IsRegularMeromorphicSection 𝒩 t}
    (Z : PrimeDivisor X)
    (Ps : Scheme.RegularMeromorphicSectionOrderPresentation ℒ s hs Z)
    (Pt : Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t ht Z) :
    keyFormulaTerm p δ n hX ℒ 𝒩 Z Ps Pt =
      (@Scheme.RegularMeromorphicSectionOrderPresentation.order X
          (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
          ℒ inferInstance s Z hs Ps) •
          mapHom (Scheme.PointClosure.ι Z.genericPoint)
            ((Scheme.PointClosure.ι Z.genericPoint ≫ p).relativeDimensionFunction δ)
            (p.relativeDimensionFunction δ) (n - 2)
            (@relativeDivisorCycle S (Scheme.PointClosure.scheme Z.genericPoint)
              (Scheme.PointClosure.ι Z.genericPoint ≫ p) inferInstance
              (AlgebraicGeometry.locallyOfFiniteType_comp
                (Scheme.PointClosure.ι Z.genericPoint) p
                (hf := inferInstanceAs (LocallyOfFiniteType
                  (Scheme.PointClosure.reducedStructure Z.genericPoint).ι)))
              δ inferInstance inferInstance
              ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj 𝒩)
              (Scheme.Modules.Invertible.pullback
                (Scheme.PointClosure.ι Z.genericPoint) inferInstance)
              (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure X
                (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
                𝒩 inferInstance t ht Z Pt)
              (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure_ne_zero X
                (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
                𝒩 inferInstance t ht Z Pt)
              (n - 2)
              (PrimeDivisor.pointClosure_relativeDimension p δ n hX Z)) -
        (@Scheme.RegularMeromorphicSectionOrderPresentation.order X
          (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
          𝒩 inferInstance t Z ht Pt) •
          mapHom (Scheme.PointClosure.ι Z.genericPoint)
            ((Scheme.PointClosure.ι Z.genericPoint ≫ p).relativeDimensionFunction δ)
            (p.relativeDimensionFunction δ) (n - 2)
            (@relativeDivisorCycle S (Scheme.PointClosure.scheme Z.genericPoint)
              (Scheme.PointClosure.ι Z.genericPoint ≫ p) inferInstance
              (AlgebraicGeometry.locallyOfFiniteType_comp
                (Scheme.PointClosure.ι Z.genericPoint) p
                (hf := inferInstanceAs (LocallyOfFiniteType
                  (Scheme.PointClosure.reducedStructure Z.genericPoint).ι)))
              δ inferInstance inferInstance
              ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ)
              (Scheme.Modules.Invertible.pullback
                (Scheme.PointClosure.ι Z.genericPoint) inferInstance)
              (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure X
                (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
                ℒ inferInstance s hs Z Ps)
              (@Scheme.RegularMeromorphicSectionOrderPresentation.restrictToPointClosure_ne_zero X
                (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
                ℒ inferInstance s hs Z Ps)
              (n - 2)
              (PrimeDivisor.pointClosure_relativeDimension p δ n hX Z)) := sorry

/-- The supports of the component terms in the key formula are locally finite when the chosen
prime divisors are locally finite. -/
theorem keyFormulaTermsLocallyFinite
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
    (ℒ 𝒩 : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.Invertible 𝒩]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {t : X.toLocallyRingedSpace.meromorphicSections 𝒩}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {ht : X.toLocallyRingedSpace.IsRegularMeromorphicSection 𝒩 t}
    {I : Type v} (Z : I → PrimeDivisor X)
    (Ps : ∀ i, Scheme.RegularMeromorphicSectionOrderPresentation ℒ s hs (Z i))
    (Pt : ∀ i, Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t ht (Z i))
    (hlocal : LocallyFinite fun i ↦ ((Z i).support : Set X)) :
    LocallyFinite fun i ↦
      (toAlgebraicCycle (p.relativeDimensionFunction δ) (n - 2)
        (keyFormulaTerm p δ n hX ℒ 𝒩 (Z i) (Ps i) (Pt i))).support := sorry

/-- The locally finite sum of the two order-weighted divisors of chosen generators equals the
boundary of the corresponding tame symbols. -/
theorem keyFormula
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
    (ℒ 𝒩 : X.Modules) [Scheme.Modules.Invertible ℒ] [Scheme.Modules.Invertible 𝒩]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (t : X.toLocallyRingedSpace.meromorphicSections 𝒩) (hs : s ≠ 0) (ht : t ≠ 0)
    {I : Type v} (Z : I → PrimeDivisor X) (hZ : Injective Z)
    (hlocal : LocallyFinite fun i ↦ ((Z i).support : Set X))
    (hs_generatorAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) →
      ∃ P : Scheme.RegularMeromorphicSectionOrderPresentation ℒ s
        ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero ℒ s).2 hs) W,
        P.quotient = 1)
    (ht_generatorAway : ∀ W : PrimeDivisor X, (∀ i, Z i ≠ W) →
      ∃ P : Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t
        ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero 𝒩 t).2 ht) W,
        P.quotient = 1)
    (Ps : ∀ i, Scheme.RegularMeromorphicSectionOrderPresentation ℒ s
      ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero ℒ s).2 hs) (Z i))
    (Pt : ∀ i, Scheme.RegularMeromorphicSectionOrderPresentation 𝒩 t
      ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero 𝒩 t).2 ht) (Z i)) :
    locallyFiniteSum (p.relativeDimensionFunction δ) (n - 2)
        (fun i ↦ keyFormulaTerm p δ n hX ℒ 𝒩 (Z i) (Ps i) (Pt i))
        (keyFormulaTermsLocallyFinite p δ n hX ℒ 𝒩 Z Ps Pt hlocal) =
      @RationalEquivalence.boundary X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - 2) I
        (fun i ↦ (Z i).genericPoint)
        (fun i ↦ PrimeDivisor.relativeDimensionFunction_genericPoint_eq
          p δ n hX (Z i))
        (fun i ↦ @PrimeDivisor.tameSymbolOnPointClosure X
          (LocallyOfFiniteType.isLocallyNoetherian p) inferInstance
          (Z i) (Ps i).quotient (Pt i).quotient)
        (PrimeDivisor.pointClosuresLocallyFinite Z hlocal) := sorry

end AlgebraicGeometry.CycleGroup
