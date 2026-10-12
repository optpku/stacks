/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Source-facing affine-open spelling for the neutral
`subobjectSectionsSubmoduleOnAffineOpen` API. -/
abbrev affineOpenSubsheafSectionsSubmodule
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : X.affineOpens) :
    Submodule Γ(X, U.1) (ℱ.val.obj (op U.1)) :=
  subobjectSectionsSubmoduleOnAffineOpen 𝒢 U

end AlgebraicGeometry.Scheme.Modules
