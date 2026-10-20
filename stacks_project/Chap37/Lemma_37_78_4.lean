/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.78.4: if a morphism of schemes is completely decomposed in the
residue-field lifting sense, locally of finite presentation, and its target is
quasi-compact and quasi-separated, then the target admits a finite family of
finite-presentation immersions whose coproduct is surjective and whose base
changes of the given morphism have sections. -/
@[stacks 0GTL]
#check (AlgebraicGeometry.Scheme.Hom.exists_finite_immersion_cover :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (∀ y : Y, ∃ σ : Spec (Y.residueField y) ⟶ X,
      σ ≫ f = Y.fromSpecResidueField y) →
    [LocallyOfFinitePresentation f] → [CompactSpace Y] → [QuasiSeparatedSpace Y] →
      ∃ n : ℕ, ∃ Z : Fin n → Scheme.{u}, ∃ z : ∀ i, Z i ⟶ Y,
        Surjective (Limits.Sigma.desc z) ∧
          (∀ i, IsImmersion (z i)) ∧
            (∀ i, AlgebraicGeometry.Scheme.Hom.FinitePresentation (z i)) ∧
              (∀ i, IsSplitEpi (pullback.snd f (z i))))
