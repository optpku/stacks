/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RegularProjectiveLine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 54.3.1: the blowup of the spectrum of a two-dimensional regular local ring at
its maximal ideal embeds as a closed subscheme of the relative projective line.  Its
exceptional divisor is the projective line over the residue field, `𝒪_X(E)` is the
degree `-1` twist, and the conormal and normal sheaves of the exceptional divisor are
respectively the degree `1` and degree `-1` twists. -/
@[stacks 0AGQ]
#check (AlgebraicGeometry.IsBlowup.exists_projectiveLine_closedImmersion_of_maximalIdeal :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))],
    let κ := IsLocalRing.ResidueField A
    let E := exceptionalIdeal (IsLocalRing.maximalIdeal A) f
    let residueProjectiveLine : ProjectiveSpace.scheme κ 1 ⟶ ProjectiveSpace.scheme A 1 :=
      (Scheme.topIso (ProjectiveSpace.scheme κ 1)).inv ≫
        ((ProjectiveSpace.scheme κ 1).isoOfEq
          (ProjectiveSpace.coefficientProjMapDomain_eq_top
            (IsLocalRing.residue A) 1).symm).hom ≫
          ProjectiveSpace.coefficientProjMap (IsLocalRing.residue A) 1
    ∃ (r : Over.mk f ⟶ Over.mk (ProjectiveSpace.toSpec A 1))
      (_ : IsClosedImmersion r.left)
      (e : E.subscheme ≅ ProjectiveSpace.scheme κ 1)
      (_ : e.hom ≫ residueProjectiveLine = E.subschemeι ≫ r.left)
      (_ : IsIsomorphic E.associatedSheaf (twistingSheaf (IsLocalRing.maximalIdeal A) f (-1)))
      (_ : IsIsomorphic (twistingSheaf (IsLocalRing.maximalIdeal A) f (-1))
        ((Scheme.Modules.pullback r.left).obj (ProjectiveSpace.twistingSheaf A 1 (-1))))
      (_ : IsIsomorphic (Scheme.Hom.conormalSheaf E.subschemeι)
        ((Scheme.Modules.pullback e.hom).obj (ProjectiveSpace.twistingSheaf κ 1 1))),
      IsIsomorphic (Scheme.Hom.normalSheaf E.subschemeι)
        ((Scheme.Modules.pullback e.hom).obj (ProjectiveSpace.twistingSheaf κ 1 (-1))))

end AlgebraicGeometry.IsBlowup
