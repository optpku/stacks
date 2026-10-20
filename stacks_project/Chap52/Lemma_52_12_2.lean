/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints
public import ReasLib.Topology.Specialization.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.AffineAlgebraizationSetup

universe u

/- Lemma 52.12.2. Under the associated-point local dimension bound, completeness, canonical
dualizing-complex existence, and the Serre-or-dimension alternative, the canonical comparison
from neighborhood sections to the inverse limit of global quotient sections is bijective. -/
@[stacks 0EIF] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.neighborhoodComparison_bijective_of_associatedPointDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_dimension : ∀ x : S.U, x ∈ associatedPoints F.obj →
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        ¬ Set.range (PointClosure.ι (S.U.ι x)) ∩
            (idealSheafDataOfIdealOnSpec S.I).support ⊆ S.U.compl →
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim
                    ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_alternative :
      coherentSatisfiesSerreConditionS
        ((coherentRestrictFunctor
          (idealOnOpen S).openComplement.ι).obj F) 1 ∨
        ringKrullDim (A ⧸ S.a) ≤ 2),
    Function.Bijective (globalNeighborhoodComparison S F.obj))
