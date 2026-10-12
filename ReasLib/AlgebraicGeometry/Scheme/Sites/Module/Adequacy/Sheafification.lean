/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineEvaluation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy
public import ReasLib.Algebra.Amitsur.Acyclic
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.FlatBaseChange

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- Affine evaluation is unchanged by sheafification on affine objects. -/
theorem affineEvaluationSheafificationIso
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S) :
    Nonempty
      (@CategoryTheory.Iso (ModuleValuedFunctor.{u, u} A)
        (ModuleValuedFunctor.category)
        (affineEvaluation ℱ A f)
        (affineEvaluation
          ((PresheafOfModules.sheafification.{u, u, u, u + 1}
            (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj ℱ).val A f)) := sorry

/-- Sheafification preserves adequacy of all affine evaluations. -/
theorem sheafification_isAdequate
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    (hℱ : ∀ (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S),
      ModuleValuedFunctor.TensorAdequate (affineEvaluation ℱ A f)) :
    ∃ (ι : Type u) (A : ι → CommRingCat.{u})
        (f : (i : ι) → Scheme.Spec.obj (op (A i)) ⟶ S),
      SemiRepresentableFamily.Over.IsCovering τ.precoverage
          (SemiRepresentableFamily.Over.ofArrows
            (fun i ↦ Scheme.Spec.obj (op (A i))) f) ∧
        ∀ i, ModuleValuedFunctor.TensorAdequate
          (affineEvaluation
            ((PresheafOfModules.sheafification.{u, u, u, u + 1}
              (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj ℱ).val
            (A i) (f i)) := sorry

end SheafOfModules
