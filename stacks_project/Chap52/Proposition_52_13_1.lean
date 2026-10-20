/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.DepthComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.AffineAlgebraizationSetup

noncomputable section

universe u

/- Proposition 52.13.1 -/
@[stacks 0EG4] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.cohomologyComparison_isIso_of_depth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace) (s : ℕ)
    (h_depth : ∀ x : S.U,
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) ∨
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + s + 1 : ℤ) : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                    (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim
                      ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_alternative :
      coherentSatisfiesSerreConditionS
        ((coherentRestrictFunctor
          (idealOnOpen S).openComplement.ι).obj F) (s + 1) ∨
        ringKrullDim (A ⧸ S.a) ≤ 2),
    ∀ i : ℕ, i < s → IsIso (Scheme.Hom.IdealPowerCohomology.Quotient.toLimit S.I S.U.ι F.obj i))

/- Proposition 52.13.1 -/
@[stacks 0EG4] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodCohomologyComparison_isIso_of_depth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace) (s : ℕ)
    (h_depth : ∀ x : S.U,
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) ∨
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + s + 1 : ℤ) : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                    (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim
                      ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_alternative :
      coherentSatisfiesSerreConditionS
        ((coherentRestrictFunctor
          (idealOnOpen S).openComplement.ι).obj F) (s + 1) ∨
        ringKrullDim (A ⧸ S.a) ≤ 2),
    IsIso (neighborhoodCohomologyComparison S F.obj s))
