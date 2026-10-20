/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/- Lemma 46.5.10 -/
@[stacks 06VP] #check (SheafOfModules.sheafification_isAdequate :
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj)
    →
    (hℱ : ∀ (A : CommRingCat.{u}) (f : Scheme.Spec.obj (op A) ⟶ S),
      ModuleValuedFunctor.TensorAdequate (affineEvaluation ℱ A f)) →
    ∃ (ι : Type u) (A : ι → CommRingCat.{u})
        (f : (i : ι) → Scheme.Spec.obj (op (A i)) ⟶ S),
      SemiRepresentableFamily.Over.IsCovering τ.precoverage
          (SemiRepresentableFamily.Over.ofArrows
            (fun i ↦ Scheme.Spec.obj (op (A i))) f) ∧
        ∀ i, ModuleValuedFunctor.TensorAdequate
          (affineEvaluation
            ((PresheafOfModules.sheafification.{u, u, u, u + 1}
              (𝟙 (StandardTopology.Big.structureSheaf τ S).obj)).obj ℱ).val
            (A i) (f i)))

end SheafOfModules
