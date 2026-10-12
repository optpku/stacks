/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 42.28.2: The operation `firstChernClassCap` descends to Chow groups;
in input degree `k + 1`, it gives the map `CH_{k + 1}(X) → CH_k(X)`. -/
@[stacks 02TI] #check (AlgebraicGeometry.ChowGroup.firstChernClassCap_chowClass :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ)
    (α : AlgebraicGeometry.CycleGroup X.left (X.hom.relativeDimensionFunction δ) k),
    AlgebraicGeometry.ChowGroup.firstChernClassCap δ X ℒ k
        (@AlgebraicGeometry.chowClass X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance k α) =
      Scheme.Modules.firstChernClassCap X.hom δ ℒ (k - 1)
        (AlgebraicGeometry.CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm α))
