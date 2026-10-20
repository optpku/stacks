/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 49.9.6
For a flat quasi-finite morphism of Noetherian schemes, the closed subscheme defined by
the different is exactly the set of points where the morphism is not étale. -/
@[stacks 0BW9] #check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_support_eq_nonEtaleAtLocus :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y] [Flat f]
      [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ),
      ((W.different τ).support : Set Y) = {y : Y | ¬ f.EtaleAt y})

#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_support_eq_nonUnramifiedAtLocus :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y] [Flat f]
      [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ),
      ((W.different τ).support : Set Y) = {y : Y | ¬ f.UnramifiedAt y})
