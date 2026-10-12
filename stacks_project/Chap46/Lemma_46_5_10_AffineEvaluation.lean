/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.AffineEvaluation
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/- Affine evaluation is the canonical module-valued functor on affine algebras. -/
#check (affineEvaluation :
    (ℱ : PresheafOfModules.{u} (StandardTopology.Big.structureSheaf τ S).obj) →
      (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
        ModuleValuedFunctor.{u, u} A)

end SheafOfModules
