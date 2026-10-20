/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.BaseChange

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 29.28.3 (1): local fibre dimension is invariant under pullback. -/
@[stacks 02FY] #check
  (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_eq_of_isPullback :
    ∀ {S X S' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
      (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsPullback g' f' f g) (x' : X'),
      f'.fiberDimensionAt x' = f.fiberDimensionAt (g' x'))

/- Lemma 29.28.3 (2): the local ring dimension of the fibre of the induced
fixed-fibre map is the difference of the two fixed-fibre stalk dimensions. -/
@[stacks 02FY] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.ringKrullDim_baseChangeFiberStalkAt_eq_sub_of_isPullback :
    ∀ {S X S' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
      (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
      (hpb : IsPullback g' f' f g) (x' : X'),
      ringKrullDim
          (AlgebraicGeometry.Scheme.Hom.baseChangeFiberStalkAt f g g' f' hpb x') =
        ((ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f' x')).unbotD 0).toNat -
          ((ringKrullDim
            (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f (g' x'))).unbotD 0).toNat)

/- Lemma 29.28.3 (3): the same local ring dimension is the difference of the
two residue-field transcendence degrees. -/
@[stacks 02FY] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.baseChangeFiberStalkDim_eq_trdeg_sub :
    ∀ {S X S' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
      (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
      (hpb : IsPullback g' f' f g) (x' : X'),
      ringKrullDim
          (AlgebraicGeometry.Scheme.Hom.baseChangeFiberStalkAt f g g' f' hpb x') =
        f.residueFieldTrdegAt (g' x') - f'.residueFieldTrdegAt x')

/- Lemma 29.28.3 (4): base change does not decrease the fixed-fibre stalk
dimension at the corresponding point. -/
@[stacks 02FY] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.ringKrullDim_fiberStalkAt_le_of_isPullback :
    ∀ {S X S' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
      (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsPullback g' f' f g) (x' : X'),
      ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f (g' x')) ≤
        ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f' x'))

/- Lemma 29.28.3 (5): the residue-field transcendence degree at the pullback
point is at most that at its image. -/
@[stacks 02FY] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.residueFieldTrdegAt_le_of_isPullback :
    ∀ {S X S' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
      (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsPullback g' f' f g) (x' : X'),
      f'.residueFieldTrdegAt x' ≤ f.residueFieldTrdegAt (g' x'))

/- Lemma 29.28.3 (6): compatible points admit a lift preserving both the
fixed-fibre stalk dimension and the residue-field transcendence degree. -/
@[stacks 02FY] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.exists_point_fiberStalkDim_eq_and_residueFieldTrdegAt_eq_of_isPullback :
    ∀ {S X S' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
      (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsPullback g' f' f g) (s' : S') (x : X), f x = g s' →
      ∃ x' : X',
        g' x' = x ∧
          f' x' = s' ∧
          ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f' x') =
              ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) ∧
            f'.residueFieldTrdegAt x' = f.residueFieldTrdegAt x)
