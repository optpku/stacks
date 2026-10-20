module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.CohomologyComparison
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.CanonicalExistence
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Serre
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a coherent module on the complement of a closed subset in an adically complete
Noetherian affine scheme with a canonical dualizing complex, the formal cohomology comparison
is invertible below degree `s` under the stalk-depth alternative and either Serre's condition
`(S_{s+1})` off the closed fiber or a quotient-ring dimension bound of two. -/
theorem cohomologyComparison_isIso_of_depth
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
        ringKrullDim (A ⧸ S.a) ≤ 2) :
    ∀ i : ℕ, i < s → IsIso (Scheme.Hom.IdealPowerCohomology.Quotient.toLimit S.I S.U.ι F.obj i) := sorry

/-- Under the stalk-depth alternative and either Serre's condition `(S_{s+1})` off the
closed fiber or a quotient-ring dimension bound of two, the formal comparison from degree-`s`
cohomology on neighborhoods of the closed fiber is invertible over an adically complete
Noetherian affine scheme with a canonical dualizing complex. -/
theorem neighborhoodCohomologyComparison_isIso_of_depth
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
        ringKrullDim (A ⧸ S.a) ≤ 2) :
    IsIso (neighborhoodCohomologyComparison S F.obj s) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
