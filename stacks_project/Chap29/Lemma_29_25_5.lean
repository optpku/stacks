/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Transitivity

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X)

/- Lemma 29.25.5: Pointwise relative flatness of a quasi-coherent module is transitive along a
morphism that is flat at the intermediate image. -/
@[stacks 01U6] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_trans f g ℱ x :
    AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ f x →
      AlgebraicGeometry.Scheme.Hom.flatAt g (f.base x) →
        AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ (f ≫ g) x)
