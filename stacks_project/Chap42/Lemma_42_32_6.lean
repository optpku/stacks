/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TensorSplitting

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.TensorSectionSplitting

open Scheme.TensorSectionSplitting

/- Lemma 42.32.6: in a tensor-section splitting over a locally finite-type
`S`-scheme `Y`, Gysin pullback along the first zero scheme after flat pullback
along the splitting projection equals flat pullback along the first line model
after Gysin pullback along the tensor-product zero scheme. -/
@[stacks 0F98] #check
  (AlgebraicGeometry.ChowGroup.TensorSectionSplitting.gysin_flatPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (delta : S → ℤ) [IsDimensionFunction delta]
      (Y : Over S) [LocallyOfFiniteType Y.hom]
      {L₁ L₂ : Y.left.Modules}
      [Scheme.Modules.Invertible L₁] [Scheme.Modules.Invertible L₂]
      {s : (L₁ ⊗ L₂).sections} (C : Scheme.TensorSectionSplitting L₁ L₂ s)
      (k : ℤ) (alpha : RelativeChow delta Y k),
      firstGysin delta Y C k (projectionPullback delta Y C k alpha) =
        firstProjectionPullback delta Y C k (baseGysin delta Y C k alpha))

end AlgebraicGeometry.ChowGroup.TensorSectionSplitting
