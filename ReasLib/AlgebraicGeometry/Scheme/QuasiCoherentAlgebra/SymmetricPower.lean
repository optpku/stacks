/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Graded

/-!
# Symmetric-power comparisons for graded quasi-coherent algebras

This file characterizes the canonical maps from symmetric powers of the degree-one piece to
the homogeneous pieces of an explicitly graded quasi-coherent algebra.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GradedQcAlgebra

variable {S : Scheme.{u}} (A : GradedQcAlgebra S)

/-- The ordered product of a finite family of degree-one local sections, formed using the
homogeneous unit and multiplication. -/
def iteratedMul (U : (Opens S)ᵒᵖ) :
    (n : ℕ) → (SymmetricPower.UFin n → (A.degreePiece 1).val.obj U) →
      (A.degreePiece n).val.obj U
  | 0, _ => A.one U
  | n + 1, x =>
      A.mul U n 1
        (iteratedMul U n (fun i ↦ x ⟨Fin.castSucc i.down⟩))
        (x ⟨Fin.last n⟩)

/-- A family of maps from symmetric powers of degree one to the homogeneous pieces is the
canonical comparison when every pure symmetric tensor maps, after the sheafification unit, to
the corresponding iterated homogeneous product. -/
def IsSymmetricPowerComparison
    (comparison : ∀ n : ℕ,
      RingedSpace.SymmetricPower.sheaf (A.degreePiece 1) n ⟶ A.degreePiece n) : Prop :=
  ∀ (n : ℕ) (U : (Opens S)ᵒᵖ)
    (x : SymmetricPower.UFin n → (A.degreePiece 1).val.obj U),
    (((comparison n).val.app U).hom
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 S.ringCatSheaf.obj)).unit.app
            (RingedSpace.SymmetricPower.presheaf (A.degreePiece 1) n)).app U
        (ModuleCat.symmetricPower.mk (R := S.presheaf.obj U) x))) =
      A.iteratedMul U n x

end AlgebraicGeometry.Scheme.GradedQcAlgebra
