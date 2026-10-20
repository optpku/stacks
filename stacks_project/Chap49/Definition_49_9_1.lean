/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Definition 49.9.1: Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of
locally Noetherian schemes. Let `ω_{Y/X}` be the relative dualizing module and let
`τ_{Y/X}` be a global section. The different of `Y/X` is the scheme-theoretic support
of `Coker(𝒪_Y ⟶ ω_{Y/X})` given by `τ_{Y/X}`, equivalently the annihilator of that
cokernel, and this annihilator is a coherent ideal sheaf of `𝒪_Y`. -/
@[stacks 0BW4] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different :
    {X Y : Scheme.{u}} → {f : Y ⟶ X} →
    [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] →
    [LocallyOfFiniteType f] → [LocallyQuasiFinite f] →
    (W : f.RelativeDualizingSheaf) → (τ : W.module.obj.sections) → Y.IdealSheafData)

#check AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_def
#check AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.differentAnnihilator_isCoherent
