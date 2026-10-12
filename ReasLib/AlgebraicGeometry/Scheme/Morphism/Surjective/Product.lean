/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.AffineProduct

/-!
# Products of surjective affine morphisms of schemes

This file records that arbitrary products of surjective affine morphisms over a
fixed base scheme are surjective.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

variable {I : Type u} (S : Scheme.{u})
variable (T : I → CategoryTheory.Over S)

/-- The structure morphism of an arbitrary product of surjective affine
morphisms over a fixed base scheme is surjective. -/
instance instSurjectivePiObjOfIsAffineHom
    [h_affine : ∀ i, IsAffineHom (T i).hom]
    [∀ i, Surjective (T i).hom] :
    Surjective (piObj T).hom := sorry

end AlgebraicGeometry.Scheme.Over
