/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap91.Lemma_91_14_2_Lift
public import stacks_project.Chap76.Lemma_76_9_7_SquareZero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Hom.GeometricNL
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The canonical free-algebra sheaf on the small étale site. -/
abbrev polynomialSheaf := FreeAlgebra.Presentation.underlying
  (commInverseImageStructureSheaf f) (Under.mk (commInverseImageStructureSheafMap f))

/-- Evaluate a polynomial in local sections at the universal sheaf generators.
This is the actual map from the geometric presentation to the ringed-topos presentation. -/
def polynomialComparison (U : (smallEtaleSite X)ᵒᵖ) :
    MvPolynomial ((commStructureSheaf X).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj U) →+* (polynomialSheaf f).obj.obj U :=
  MvPolynomial.eval₂Hom
    ((FreeAlgebra.Presentation.base (commInverseImageStructureSheaf f)
      (Under.mk (commInverseImageStructureSheafMap f))).hom.app U).hom
    (fun x ↦ (FreeAlgebra.Presentation.generator (commInverseImageStructureSheaf f)
      (Under.mk (commInverseImageStructureSheafMap f))).hom.app U x)

@[simp] theorem polynomialComparison_C (U : (smallEtaleSite X)ᵒᵖ)
    (a : (commInverseImageStructureSheaf f).obj.obj U) :
    polynomialComparison f U (MvPolynomial.C a) =
      ((FreeAlgebra.Presentation.base (commInverseImageStructureSheaf f)
        (Under.mk (commInverseImageStructureSheafMap f))).hom.app U).hom a := by
  simp [polynomialComparison]

@[simp] theorem polynomialComparison_X (U : (smallEtaleSite X)ᵒᵖ)
    (x : (commStructureSheaf X).obj.obj U) :
    polynomialComparison f U (MvPolynomial.X x) =
      (FreeAlgebra.Presentation.generator (commInverseImageStructureSheaf f)
        (Under.mk (commInverseImageStructureSheafMap f))).hom.app U x := by
  simp [polynomialComparison]

/-- Evaluation in O_X agrees with the original polynomial presentation. -/
theorem polynomialComparison_evaluation (U : (smallEtaleSite X)ᵒᵖ) :
    (((FreeAlgebra.Presentation.map (commInverseImageStructureSheaf f)
      (Under.mk (commInverseImageStructureSheafMap f))).hom.app U).hom).comp
        (polynomialComparison f U) =
      MvPolynomial.eval₂Hom ((commInverseImageStructureSheafMap f).hom.app U).hom id := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, polynomialComparison_C]
    have h := congrArg (fun q => (q.hom.app U).hom a)
      (FreeAlgebra.evaluation_base (Under.mk (commInverseImageStructureSheafMap f))
        (FreeAlgebra.Presentation.generators (Under.mk (commInverseImageStructureSheafMap f))) (𝟙 _))
    exact h.trans (MvPolynomial.eval₂Hom_C _ id a).symm
  · intro x
    simp only [RingHom.comp_apply, polynomialComparison_X]
    have h := congrArg (fun q => q.hom.app U x)
      (FreeAlgebra.evaluation_generator (Under.mk (commInverseImageStructureSheafMap f))
        (FreeAlgebra.Presentation.generators (Under.mk (commInverseImageStructureSheafMap f))) (𝟙 _))
    exact h.trans (MvPolynomial.eval₂Hom_X' _ id x).symm

end AlgebraicGeometry.AlgebraicSpace.Hom.GeometricNL
