/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.AffineSpace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

/-
Lemma 28.18.6: A quasi-affine scheme admits a morphism from an affine scheme whose pullback along
every affine scheme over it is a fixed finite-dimensional relative affine space over that base.
-/
@[stacks 0F82] #check (AlgebraicGeometry.Scheme.IsQuasiAffine.exists_affineSpacePullback :
  ∀ {X : Scheme.{u}}, X.IsQuasiAffine →
    ∃ (n : ℕ) (T : Scheme.{u}) (π : T ⟶ X),
      IsAffine T ∧
      ∀ {X' : Scheme.{u}} (f : X' ⟶ X), IsAffine X' →
        Nonempty (Over.mk (pullback.snd π f) ≅
          Over.mk (𝔸(ULift.{u} (Fin n); X') ↘ X')))

end AlgebraicGeometry.Scheme.IsQuasiAffine
