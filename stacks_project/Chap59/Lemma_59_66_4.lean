/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantFiltration
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.66.4: a finite-type locally constant module sheaf annihilated by a
positive prime power admits a constant finite-module filtration after a finite étale
pullback of degree prime to that prime on an irreducible geometrically unibranch scheme. -/
@[stacks 0GJ0] #check
  (AlgebraicGeometry.Scheme.exists_finiteEtale_pullback_constant_filtration :
    ∀
    {S : Scheme.{u}} [IrreducibleSpace S] (huni : S.isGeometricallyUnibranch)
    (ell n : ℕ) [Fact (Nat.Prime ell)] (hn : 1 ≤ n)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ T : Scheme.{u},
      HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ (T : Scheme.{u}) (U : T.Etale),
      HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ {T : Scheme.{u}} (f : T ⟶ S)
      (P : S.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ T : Scheme.{u},
      HasCokernels (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [∀ T : Scheme.{u},
      HasZeroObject (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (h_ann : (ell ^ n : ℕ) • 𝟙 F = 0),
    ∃ (T : Scheme.{u}) (f : T ⟶ S),
      finiteEtaleMorphism f ∧ FiniteEtale.IsConstantDegreePrimeTo f ell ∧
        ∃ s : RelSeries
            ({p : Subobject (smallEtaleCommModuleSheafPullback f F) ×
                Subobject (smallEtaleCommModuleSheafPullback f F) |
              hasConstantFiniteModuleSuccessiveQuotient p.1 p.2} : SetRel _ _),
          IsZero (Subobject.underlying.obj s.head) ∧ IsIso s.last.arrow)
