/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.FiniteCover

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

/- Lemma 59.80.9 (1): an affine scheme admits an integral surjective cover on
which every closed subscheme has vanishing positive-degree small-étale
cohomology with finite constant coefficients. -/
@[stacks 09ZD] #check
  (AlgebraicGeometry.Scheme.Hom.exists_integralSurjective_etaleHq_constantFinite_isZero :
    ∀ {X : Scheme.{u}}, [IsAffine X] →
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
        IsIntegralHom f ∧ Surjective f ∧
          ∀ {Z' : Scheme.{u}} (i' : Z' ⟶ X') [IsClosedImmersion i']
            (M : AddCommGrpCat.{u}) [Finite M]
            (q : ℕ) (hq : 1 ≤ q),
            IsZero
              ((Sheaf.functorH Z'.smallEtaleTopology q).obj
                ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M)))

/- Lemma 59.80.9 (2): every positive-degree small-étale cohomology class of a
finite constant sheaf on a closed subscheme of an affine scheme is killed after
a finite surjective finite-presentation base change. -/
@[stacks 09ZD] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finiteFpSurjective_etaleHq_eq_zero :
    ∀ {X Z : Scheme.{u}}, [IsAffine X] → (i : Z ⟶ X) → [IsClosedImmersion i] →
      (M : AddCommGrpCat.{u}) → [Finite M] → (q : ℕ) → 1 ≤ q →
      (ξ : (Sheaf.functorH Z.smallEtaleTopology q).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)) →
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
        IsFinite f ∧ Surjective f ∧ AlgebraicGeometry.Scheme.Hom.FinitePresentation f ∧
          AlgebraicGeometry.Scheme.Hom.etaleHq_constant_pullback
            (pullback.snd f i) M q ξ = 0)
