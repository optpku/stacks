/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- The tensor-section splitting API is owned by its reusable mathematical
module; this typed check preserves the source-side compatibility surface. -/
#check (AlgebraicGeometry.Scheme.existsTensorSectionSplitting :
  ∀ (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
      [Modules.Invertible L₁] [Modules.Invertible L₂]
      (s : (L₁ ⊗ L₂).sections),
    ∃ C : TensorSectionSplitting L₁ L₂ s,
      ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y),
        ∃ C' : TensorSectionSplitting ((Modules.pullback g).obj L₁)
          ((Modules.pullback g).obj L₂) (Modules.pullbackTensorSection g s),
          Nonempty (C.BaseChange g C'))

end AlgebraicGeometry.Scheme
