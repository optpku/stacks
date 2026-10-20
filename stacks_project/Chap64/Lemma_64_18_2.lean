/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Eventual
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Lemma 64.18.2: on a Noetherian scheme X, an inverse system {G_n}_{n ≥ 1} of
constructible ZMod (ℓ^n)-modules whose reductions G_n / ℓ^k G_n are eventually
constant for every k ≥ 1 has eventual values F_k assembling into a ℤ_[ℓ]-sheaf. -/
@[stacks 03UN] #check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.ofEventuallyConstant (X := X) (ℓ := ℓ) :
    ∀ (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})),
      (∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0) →
      (∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n)) →
      G.IsEventuallyConstantModNsmul ℓ → ZEllSheaf X ℓ)
