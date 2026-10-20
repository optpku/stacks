/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Topology.KrullDimension.Local
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

noncomputable section

universe u

/- Lemma 29.28.7 (1): a specialization in a fibre can only increase the local topological
Krull dimension. -/
@[stacks 06RU] #check
  (Specializes.topologicalKrullDimAt_le :
    ∀ {T : Type u} [TopologicalSpace T] {x x' : T},
      Specializes x x' → topologicalKrullDimAt x ≤ topologicalKrullDimAt x')

/- Lemma 29.28.7 (2): for a locally finite type morphism, a proper specialization in a fixed
fibre strictly increases the Krull dimension of the local ring. -/
@[stacks 06RU] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.ringKrullDim_stalk_lt_of_specializes :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
        [AlgebraicGeometry.LocallyOfFiniteType f] {s : S} {x x' : f.fiber s},
      Specializes x x' → x ≠ x' →
        ringKrullDim ((f.fiber s).presheaf.stalk x) <
          ringKrullDim ((f.fiber s).presheaf.stalk x'))

/- Lemma 29.28.7 (3): for a locally finite type morphism, a proper specialization in a fixed
fibre strictly decreases the residue-field transcendence degree over the base residue field. -/
@[stacks 06RU] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.trdeg_residueField_gt_of_specializes :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
        [AlgebraicGeometry.LocallyOfFiniteType f] {s : S} {x x' : f.fiber s},
      Specializes x x' → x ≠ x' →
        Cardinal.toNat (Algebra.trdeg (S.residueField s) ((f.fiber s).residueField x)) >
          Cardinal.toNat (Algebra.trdeg (S.residueField s) ((f.fiber s).residueField x')))
