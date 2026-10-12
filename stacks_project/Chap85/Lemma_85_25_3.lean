/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_25_1_Forget
public import stacks_project.Chap85.Lemma_85_25_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_25_3_Derived

/-!
# Lemma 85.25.3

If `a : U ⟶ X` is a proper hypercovering in `LCCat`, then for `K` in `D⁺(X)`
the canonical derived unit `K ⟶ Ra_* a⁻¹ K` is an isomorphism, where `a` is the
Lemma 85.2.8 Zariski augmentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [(augmentationPushforward (toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]

/-- Lemma 85.25.3. Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X` be an
augmentation. If `a` gives a proper hypercovering of `X`, then for `K` in `D⁺(X)` the
canonical derived unit `K ⟶ Ra_* (a⁻¹ K)` is an isomorphism, where `a` is the
Lemma 85.2.8 Zariski augmentation `augmentationMorphism (toTopCatAugmentation a)`. -/
@[stacks 09XS]
theorem plusDerivedUnit_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})) :
    IsIso ((plusDerivedUnit (toTopCatAugmentation a)).app K) :=
  sorry

/-- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism of functors on `D⁺(X)`. -/
theorem plusDerivedUnit_isIso (ha : IsProperHypercovering a) :
    IsIso (plusDerivedUnit (toTopCatAugmentation a)) :=
  sorry

end LCCat

end
