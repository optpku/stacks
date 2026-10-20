/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantFiltration
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.66.2. A finite-type locally constant sheaf of `F_ℓ`-vector spaces on a
connected scheme admits a filtration by constant rank-one sheaves after pullback
along a finite étale morphism of degree prime to `ℓ`. -/
@[stacks 0A3R] #check
  (AlgebraicGeometry.Scheme.exists_finiteEtale_pullback_constantZModFiltration :
    ∀ {ℓ : ℕ} {S : Scheme.{u}} [ConnectedSpace S] [Fact (Nat.Prime ℓ)]
    [∀ T : Scheme.{u},
      HasWeakSheafify T.smallEtaleTopology (ModuleCat (ZMod ℓ))]
    [∀ U : S.Etale,
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat (ZMod ℓ))]
    [∀ {T : Scheme.{u}} (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ ModuleCat (ZMod ℓ)),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology (ModuleCat (ZMod ℓ)))
    [Sheaf.IsFiniteTypeLocallyConstantModule F],
    ∃ (T : Scheme.{u}) (f : T ⟶ S),
      IsFinite f ∧ Etale f ∧ FiniteEtale.IsConstantDegreePrimeTo f ℓ ∧
        ∃ s : RelSeries
            ({p : Subobject (smallEtaleModuleSheafPullback f F) ×
                Subobject (smallEtaleModuleSheafPullback f F) |
              hasConstantZModSuccessiveQuotient p.1 p.2} : SetRel _ _),
          IsZero (Subobject.underlying.obj s.head) ∧
            Nonempty
              (Subobject.underlying.obj s.last ≅
                smallEtaleModuleSheafPullback f F))
