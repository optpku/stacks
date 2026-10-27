/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.SchemeComparison

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj SheafOfModules.RingedSite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)

/- Lemma 71.11.4. The canonical homomorphism from the pulled-back graded algebra
into the nonnegative canonical Serre twists, with its unit and multiplication laws. -/
@[stacks 084D] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.psi F hF : CanonicalTwists.CanonicalHom F hF)

#check (CanonicalTwists.CanonicalHom.spec_of (CanonicalTwists.psi F hF) :
  CanonicalTwists.CanonicalHom.spec (CanonicalTwists.psi F hF))

#check (CanonicalTwists.obj_isQuasicoherent F hF :
  ∀ n : ℤ, (CanonicalTwists.obj F hF n).IsQuasicoherent)

#check (algebra_isQuasicoherent F hF : (CanonicalTwists.algebra F hF).IsQuasicoherent)

#check (psi_baseChange F hF :
  ∀ {Z : Over S} (g : ofOver Z ⟶ X) (U : Z.left.affineOpens)
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ),
    CanonicalTwists.affineChartPsiComparison g F hF U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg F U) d n =
      CanonicalTwists.affineChartPsiModel g F hF U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg F U) d n)
