/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Affine
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

@[expose] public section

universe u

/- Lemma 60.18.1: in Situation 60.7.5, a locally quasi-coherent module sheaf on
the small crystalline site has vanishing positive-degree cohomology over every
object whose thickening or source is affine. -/
@[stacks 07JJ] #check
  (AlgebraicGeometry.Scheme.Crystalline.higherCohomology_isZero_of_affine :
    ∀ {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
      (F : CrystallineModuleSheaf.CrisModuleSheaf
        B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
      (hF : CrystallineModuleSheaf.IsCrisSheaf p B.toSpec B.prime_nilpotent F)
      (h_quasiCoherent : CrystallineModuleSheaf.CrisModuleSheaf.IsLocallyQuasiCoherent F)
      (A : smallCrystallineSite
        B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
      (h_affine : IsAffine A.obj.1.thickening ∨ IsAffine A.obj.1.source.left)
      (q : ℕ) (hq : 0 < q),
      IsZero
        ((hF.abelianSheafULift p B.toSpec B.prime_nilpotent).cohomologyOverObject.{u + 1, u + 1} A q))
