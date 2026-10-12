/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericPoints.FunctionField
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 42.16.2: a proper dominant morphism of integral schemes that induces a finite
extension of function fields is finite over an open neighborhood of any target point whose
local ring has dimension one, provided the target is locally Noetherian. -/
@[stacks 02RM] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_finiteFunctionFieldExtension :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
      [IsProper f] [IsDominant f] (ξ : Y)
      (hfinite : f.FiniteFunctionFieldExtension)
      (hξ : ringKrullDim (Y.presheaf.stalk ξ) = 1),
      ∃ V : Y.Opens, ξ ∈ V ∧ IsFinite (f ∣_ V))
