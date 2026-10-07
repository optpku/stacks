module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.Gysin

open CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ)

/- Definition 42.29.1: the Gysin homomorphism from degree-`k + 1` cycles on `X` to
degree-`k` Chow classes on the zero scheme of `s`. -/
@[stacks 02T8] #check (AlgebraicGeometry.Scheme.Modules.gysin p δ ℒ s k :
  CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
    @ChowGroup (zeroScheme ℒ s)
      (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
        ℒ inferInstance s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k)

/- On an integral generator not contained in the zero scheme, Gysin intersection is the
cycle of the scheme-theoretic intersection. -/
#check (AlgebraicGeometry.Scheme.Modules.gysin_point_of_not_mem p δ ℒ s k :
  ∀ (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
      (hmem : x ∉ (zeroIdealSheaf ℒ s).support),
    gysin p δ ℒ s k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
          (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (zeroPointIntersectionFundamentalCycle p δ ℒ s k x)))

/- On an integral generator contained in the zero scheme, Gysin intersection is the
pushforward of first-Chern intersection on that generator. -/
#check (AlgebraicGeometry.Scheme.Modules.gysin_point_of_mem p δ ℒ s k :
  ∀ (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
      (hmem : x ∈ (zeroIdealSheaf ℒ s).support),
    gysin p δ ℒ s k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (CycleGroup.mapHom (pointClosureToZeroScheme ℒ s x hmem)
          ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ)
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (@firstChernCycle (Scheme.PointClosure.scheme x)
            (@Scheme.PointClosure.scheme_isLocallyNoetherian X
              (LocallyOfFiniteType.isLocallyNoetherian p) x)
            ((Scheme.PointClosure.ι x ≫ p).relativeDimensionFunction δ) inferInstance
            ((pullback (Scheme.PointClosure.ι x)).obj ℒ) inferInstance k
            (pointClosureFundamentalCycle p δ k x hx))))

/- The Gysin map extends the two generator rules by a locally finite linear sum. -/
#check (AlgebraicGeometry.Scheme.Modules.gysinCycle_apply p δ ℒ s k :
  ∀ (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1))
      (z : zeroScheme ℒ s),
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (gysinCycle p δ ℒ s k α) z =
      ∑ᶠ x : X,
        CycleGroup.toAlgebraicCycle
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (if hx : p.relativeDimensionFunction δ x = k + 1 then
            (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
              gysinGeneratorCycle p δ ℒ s k x hx
          else 0) z)

section Cartier

variable [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)]

/- Effective-Cartier intersection is proper pushforward of the Gysin class along the
zero-scheme immersion. -/
#check (AlgebraicGeometry.Scheme.Modules.cartierIntersection_apply p δ ℒ s k :
  ∀ α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1),
    cartierIntersection p δ ℒ s k α =
      ChowGroup.map δ (Over.mk (zeroSchemeι ℒ s ≫ p)) (Over.mk p)
        (Over.homMk (zeroSchemeι ℒ s) rfl) k (gysin p δ ℒ s k α))

end Cartier

end AlgebraicGeometry.Scheme.Modules
