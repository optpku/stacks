/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (K : Complex (J := J) (O := O))
variable (ι : Type w)

/- Lemma 22.35.1 (09LV) (1): a complex `K` on a ringed site defines the DG functor
`- ⊗_(endDGA K) K`. -/
@[stacks 09LV] #check
  (tensorFunctor K : DifferentialGradedCategory.DgFunctor ℤ (Modules K)
    (Complex (J := J) (O := O)))

/- Lemma 22.35.1 (09LV) (2): this functor sends the regular `endDGA K`-module to `K`. -/
@[stacks 09LV] #check
  (objRegularIso K : (tensorFunctor K).obj (endDGA K).regularModule ≅ K)

/- Lemma 22.35.1 (09LV) (3): this functor preserves arbitrary direct sums. -/
@[stacks 09LV] #check
  (preservesCoproducts K ι :
    PreservesColimitsOfShape (Discrete ι) (tensorFunctor K).mapComp)
