/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.PurelyInseparable
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.6.5 (1): geometric reducedness at a point can be checked after every finite purely
inseparable field extension. -/
@[stacks 035Y] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt.iff_forall_isReduced_stalk_finitePurelyInseparable :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (p : ℕ) [Fact p.Prime] [CharP k p] (x : X.left),
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x ↔
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
            [IsPurelyInseparable k k'],
          ∀ x' : AlgebraicGeometry.FieldExtension.baseChange k k' X.hom,
            AlgebraicGeometry.FieldExtension.toSource k k' X.hom x' = x →
              _root_.IsReduced
                ((AlgebraicGeometry.FieldExtension.baseChange k k' X.hom).presheaf.stalk x'))

/- Lemma 33.6.5 (2): geometric reducedness at a point can be checked after adjoining first pth
roots of the base field. -/
@[stacks 035Y] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt.iff_isReduced_stalk_onePthRootExtension :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (p : ℕ) [Fact p.Prime] [CharP k p] (x : X.left),
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x ↔
        ∀ x' : AlgebraicGeometry.FieldExtension.baseChange k
            (IntermediateField.onePthRootExtension k p) X.hom,
          AlgebraicGeometry.FieldExtension.toSource k
              (IntermediateField.onePthRootExtension k p) X.hom x' = x →
            _root_.IsReduced
              ((AlgebraicGeometry.FieldExtension.baseChange k
                (IntermediateField.onePthRootExtension k p) X.hom).presheaf.stalk x'))

/- Lemma 33.6.5 (3): geometric reducedness at a point can be checked after passing to the perfect
closure of the base field. -/
@[stacks 035Y] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt.iff_isReduced_stalk_perfectClosure :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (p : ℕ) [Fact p.Prime] [CharP k p] (x : X.left),
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x ↔
        ∀ x' : AlgebraicGeometry.FieldExtension.baseChange k
            (perfectClosure k (AlgebraicClosure k)) X.hom,
          AlgebraicGeometry.FieldExtension.toSource k
              (perfectClosure k (AlgebraicClosure k)) X.hom x' = x →
            _root_.IsReduced
              ((AlgebraicGeometry.FieldExtension.baseChange k
                (perfectClosure k (AlgebraicClosure k)) X.hom).presheaf.stalk x'))
