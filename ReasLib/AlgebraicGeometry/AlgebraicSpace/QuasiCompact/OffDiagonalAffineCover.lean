/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FibrePower.OffDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient.Torsor

/-!
# Bounded affine covers of off-diagonal quotients

Quasi-compact quasi-separated algebraic spaces admit bounded affine étale atlases
and bounded affine étale covers of the associated off-diagonal free quotients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `X` is a quasi-compact quasi-separated algebraic space over
`S`, there exist an affine scheme `U`, a surjective étale morphism
`f : ofOver U ⟶ X`, an integer `d` with `degreesOfFibresBoundedBy f d`, and for
every `p : Fin (d + 1)` a free quotient `q p : offDiagonal f (p.val + 1) ⟶ Up p`
of `offDiagonalPermLift f (p.val + 1)` over `X` together with a surjective étale
morphism `g p : ofOver (Vp p) ⟶ Up p` from an affine scheme and an integer
`dp p` with `degreesOfFibresBoundedBy (g p) (dp p)`. -/
@[stacks 072C]
theorem exists_affineEtale_offDiagonalAffineCover
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ (U : Over S) (f : ofOver U ⟶ X) (d : ℕ),
      AlgebraicGeometry.IsAffine U.left ∧ Etale f ∧ Surjective f ∧ Separated f ∧
        degreesOfFibresBoundedBy f d ∧
        ∀ [Separated f],
          ∃ (Up : Fin (d + 1) → AlgebraicSpace S)
            (q : ∀ p, offDiagonal f (p.val + 1) ⟶ Up p)
            (π : ∀ p, Up p ⟶ X)
            (Vp : Fin (d + 1) → Over S)
            (g : ∀ p, ofOver (Vp p) ⟶ Up p)
            (dp : Fin (d + 1) → ℕ),
            (∀ p, IsFreeQuotient (offDiagonalPermLift f (p.val + 1)) (q p)) ∧
              (∀ p, Etale (π p)) ∧
              (∀ p, q p ≫ π p = offDiagonalToBase f (p.val + 1)) ∧
              (∀ p, AlgebraicGeometry.IsAffine (Vp p).left) ∧
              (∀ p, Etale (g p)) ∧ (∀ p, Surjective (g p)) ∧
              (∀ p, degreesOfFibresBoundedBy (g p) (dp p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
