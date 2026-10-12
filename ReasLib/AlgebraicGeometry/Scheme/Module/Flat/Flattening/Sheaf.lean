/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# The fpqc sheaf property for the flattening functor

This module records fpqc descent for the functor detecting flatness after scheme base change.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The flattening functor of a quasicoherent module is an fpqc sheaf. -/
theorem functor_isSheaf_fpqc :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (functor f ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
