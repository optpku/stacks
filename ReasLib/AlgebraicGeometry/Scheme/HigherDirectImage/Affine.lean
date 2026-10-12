/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The positive-degree higher direct images of a quasi-coherent module along an affine
morphism of schemes vanish. -/
@[stacks 01XC]
theorem higherDirectImageModule_isZero_of_isAffineHom
    (f : X ⟶ S) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ) := sorry

end AlgebraicGeometry.Scheme
