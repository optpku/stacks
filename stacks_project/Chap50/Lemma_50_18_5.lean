/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.LocalComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.18.5: for every point of the upper-left scheme in an open-pullback
commutative square whose right edge is locally quasi-finite and syntomic, there are
compatible open neighborhoods carrying comparison maps in every degree that satisfy
the unit, wedge, and base-change conditions. -/
@[stacks 0H9H] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.exists_localCompatibleComparison :
    ∀ {X' X Y' Y : Scheme.{u}}
      (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
      (sq : CommSq b f' f a),
      [IsOpenImmersion (pullback.lift b f' sq.w)] →
      [LocallyQuasiFinite f] → [Syntomic f] → (y' : Y') →
      ∃ (V' : Y'.Opens) (V : Y.Opens) (U' : X'.Opens) (U : X.Opens),
        ∃ (hy' : y' ∈ V')
          (hb : V' ≤ b ⁻¹ᵁ V) (hf' : V' ≤ f' ⁻¹ᵁ U')
          (ha : U' ≤ a ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ U),
          ∀ P : AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero.Determinant.Pullback
              (b.resLE V V' hb),
            Nonempty
              (AlgebraicGeometry.Scheme.RelativeDifferentials.CompatibleComparison
                (h_open := AlgebraicGeometry.Scheme.Pullback.restrictedLiftIsOpenImmersion
                  b f' f a sq V' V U' U hb hf' hf ha)
                (h_syntomic :=
                  AlgebraicGeometry.Scheme.Hom.syntomic_resLE_of_syntomic
                    f (inferInstance) hf)
                (b.resLE V V' hb) (f'.resLE U' V' hf')
                (f.resLE U V hf) (a.resLE U U' ha)
                (AlgebraicGeometry.Scheme.Pullback.restrictedCommSq
                  b f' f a sq V' V U' U hb hf' hf ha) P))
