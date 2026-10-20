module

public import stacks_project.Chap52.Lemma_52_12_2
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.AffineAlgebraizationSetup

noncomputable section

universe u

/- Proposition 52.12.3 -/
@[stacks 0EG2] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.globalNeighborhoodComparison_bijective_of_associatedPointDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (S : AffineAlgebraizationSetup A)
      (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
      [IsAdicComplete S.I A]
      (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace),
      (∀ x : S.U, x ∈ associatedPoints F.obj →
        S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
          ¬ Set.range (PointClosure.ι (S.U.ι x)) ∩
              (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
            ∀ z : PointClosure.scheme (S.U.ι x),
              PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
                ((Ideal.LocalCohomology.dimension S.I
                    S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim
                      ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z))) →
      Function.Bijective (globalNeighborhoodComparison S F.obj))
