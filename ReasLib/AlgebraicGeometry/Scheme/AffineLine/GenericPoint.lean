/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.FieldTheory.RatFunc.Localization

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Every morphism from the rational-function generic point to a finite-type scheme over a field
extends to a principal open subscheme of the affine line. -/
theorem exists_hom_from_ratFunc {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [QuasiCompact sX] [LocallyOfFiniteType sX]
    (φ : Spec (.of (RatFunc k)) ⟶ X)
    (hφ : φ ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k)))) :
    ∃ (f : Polynomial k) (hf : f ≠ 0) (ψ : Spec (.of (Localization.Away f)) ⟶ X),
      ψ ≫ sX =
          Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (Localization.Away f))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
        φ = Spec.map (CommRingCat.ofHom (RatFunc.fromAway hf)) ≫ ψ := sorry

end AlgebraicGeometry.Scheme
