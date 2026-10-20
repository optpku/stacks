/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.ClassGroup
import StacksCheckRecall

/-!
# Example 72.6.10

The affine-line involution space is smooth over `k`, Noetherian and integral of
dimension one, and has Weil divisor class group `ℤ/2ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- (1) the algebraic space is smooth over its base field in the
étale-square sense. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.smooth_toBase :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)], isSmoothOverBase k)

/- (2) the descended squaring morphism is a universal homeomorphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.universalHomeomorphism_toAffineLine :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    AlgebraicGeometry.AlgebraicSpace.Sheaf.isUniversalHomeomorphism (toAffineLine k))

/- (3) the morphism is an isomorphism away from the origin. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.isIso_over_punctured :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    IsIso (pullback.snd (toAffineLine k)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (puncturedι k))))

/- (4) the Noetherian atlas and quasi-compact diagonal certify
Noetherianity of the quotient. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.isNoetherian :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    AlgebraicGeometry.IsNoetherian (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj))

/- (5) the integral atlas and quasi-compact diagonal certify
integrality of the quotient via the étale-surjective atlas. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.isIntegral :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    AlgebraicGeometry.IsIntegral (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj))

/- (6) the étale-local dimension is one. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.dimension_eq_one :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)], dimension k = 1)

/- (7) prime divisors are the closed points, indexed on the target
affine line through the universal homeomorphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.closedPoint_iff_exists_primeDivisor :
  ∀ (k : Type u) [Field k] (x : (cover k).left),
    x ∈ closedPoints (cover k).left ↔
      ∃ Z : AlgebraicGeometry.PrimeDivisor (cover k).left, Z.genericPoint = x)

/- (8) the fibre over the origin has exactly one field-valued point. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.unique_point_over_origin :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] (σ : Spec (CommRingCat.of K) ⟶ base k),
    Nonempty
      ((pullback (toAffineLine k)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
          (originToCover k))).obj.obj (op (Over.mk σ))) ∧
    Subsingleton
      ((pullback (toAffineLine k)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
          (originToCover k))).obj.obj (op (Over.mk σ))))

/- (9) every closed point away from the origin has zero divisor class. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.class_eq_zero_of_ne_origin :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)]
    {Z : AlgebraicGeometry.PrimeDivisor (cover k).left},
    Z ≠ originPrimeDivisor k → classGroupMk k (WeilDivisor.single Z) = 0)

/- (10) the divisor of the target coordinate is twice the origin. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.principalWeilDivisor_coordinate :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    principalWeilDivisor k (coordinate k) = 2 • originWeilDivisor k)

/- Example 72.6.10 (11): the origin class identifies the divisor class group with ℤ/2ℤ. -/
@[stacks 0ENT] #check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.classGroupEquivZMod :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)], classGroup k ≃+ ZMod 2)
