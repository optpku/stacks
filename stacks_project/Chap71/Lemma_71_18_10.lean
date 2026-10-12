/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_5_1_FittingIdeal

/-!
# Lemma 71.18.10

If a finite-type quasi-coherent module on an algebraic space is locally free of
rank `k` off the closed subspace cut out by `Fit_k(F)`, then its strict
transform under the blowup in that subspace is locally free of rank `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf

/-- The `k`th Fitting ideal of a finite-type quasi-coherent module is a
quasi-coherent ideal subobject. -/
instance instIsQuasiCoherent {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : B.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ) :
    IsQuasiCoherent (fittingIdealSheaf F k) :=
  sorry

/-- Lemma 71.18.10: if `F` is a finite-type quasi-coherent `𝒪_B`-module on an
algebraic space `B` over a scheme `S`, `Z_k ⊂ B` is the closed subspace cut out
by `Fit_k(F)`, and `F` is locally free of rank `k` on `B \ Z_k`, then for a
chosen blowup `π : B' ⟶ B` of `B` in `Z_k` the strict transform `F'` of `F` is
locally free of rank `k`. -/
@[stacks 0D0Q, instance]
instance strictTransformModule_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} {B : AlgebraicSpace S} (F : B.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ)
    (π : Blowup B (fittingIdealSheaf F k))
    [SheafOfModules.IsFiniteLocallyFreeOfRank k
      ((Modules.pullback (closedImmersionComplementι
          (Blowup.center (fittingIdealSheaf F k)).ι)).obj F)] :
    SheafOfModules.IsFiniteLocallyFreeOfRank k
      (strictTransformModule π.hom (Blowup.exceptionalDivisor π) (𝟙 B) F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf
