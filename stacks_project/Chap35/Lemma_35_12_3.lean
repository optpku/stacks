/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.DirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 35.12.3 (1): the direct image of a parasitic module sheaf along a
scheme morphism is parasitic on the corresponding standard big site. -/
@[stacks 07AG] #check
  (SheafOfModules.IsParasiticOne.modulePushforward :
    ∀ {S T : Scheme.{u}} (τ : StandardTopology) (f : T ⟶ S)
      {ℱ : RingedSite.ModuleCat.{u + 1}
        (StandardTopology.Big.ringedSite τ T)},
      SheafOfModules.IsParasiticOne ℱ →
      SheafOfModules.IsParasiticOne
        ((StandardTopology.Big.pullbackRingedHom τ f).modulePushforward.obj ℱ))

/- Lemma 35.12.3 (2): every higher direct image of a parasitic module sheaf
along a scheme morphism is parasitic on the corresponding standard big site. -/
@[stacks 07AG] #check
  (SheafOfModules.IsParasiticOne.higherDirectImageModule :
    ∀ {S T : Scheme.{u}} (τ : StandardTopology) (f : T ⟶ S)
      {ℱ : RingedSite.ModuleCat.{u + 1}
        (StandardTopology.Big.ringedSite τ T)},
      SheafOfModules.IsParasiticOne ℱ → ∀ i : ℕ,
      SheafOfModules.IsParasiticOne
        (StandardTopology.Big.higherDirectImageModule τ f ℱ i))
