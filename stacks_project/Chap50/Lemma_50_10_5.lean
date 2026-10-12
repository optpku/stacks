/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LineBundle
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.10.5 (1) -/
@[stacks 0FUI] #check
  (AlgebraicGeometry.Scheme.DeRham.associatedLineBundleDeRhamComparison_quasiIso :
    ∀ {S X : Scheme.{u}}
      (g : S ⟶ AlgebraicGeometry.Spec
        (CommRingCat.of (ULift.{u} ℚ))) (f : X ⟶ S) (ℒ : X.Modules)
      [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver
        (Scheme.SymmetricAlgebra.qcAlgebra ℒ)) [Scheme.IsRelativeSpectrumOver P],
      QuasiIso
        (AlgebraicGeometry.RingedSpace.DeRham.map
          (CategoryTheory.CommSq.mk
            (AlgebraicGeometry.Scheme.DeRham.associatedLineBundleSquare_w f ℒ P))))

/- Lemma 50.10.5 (2) -/
@[stacks 0FUI] #check
  (AlgebraicGeometry.Scheme.DeRham.associatedLineBundleDeRhamCohomology_isomorphic :
    ∀ {S X : Scheme.{u}}
      (g : S ⟶ AlgebraicGeometry.Spec
        (CommRingCat.of (ULift.{u} ℚ))) (f : X ⟶ S) (ℒ : X.Modules)
      [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver
        (Scheme.SymmetricAlgebra.qcAlgebra ℒ)) [Scheme.IsRelativeSpectrumOver P]
      (n : ℤ),
      CategoryTheory.IsIsomorphic
        (AddCommGrpCat.of
          (AlgebraicGeometry.Scheme.DeRham.cohomology f n))
        (AddCommGrpCat.of
          (AlgebraicGeometry.Scheme.DeRham.cohomology
            (AlgebraicGeometry.Scheme.associatedVectorBundleπ ℒ P ≫ f) n)))
