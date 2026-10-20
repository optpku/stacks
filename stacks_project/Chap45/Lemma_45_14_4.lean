/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

/- Lemma 45.14.4 -/
@[stacks 0FII] #check (WeilCohomology.CycleClass.closedSubscheme_mul_eq_zero :
    ∀ {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
      {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
      {V : Type w} [Category.{z} V]
      {dimension : V → ℕ} {product : V → V → V}
      {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
      {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
      {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
      {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
      {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
      {pointCycle : CHgrade point 0} {H Picard : V → Type x}
      [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
      (T : WeilCohomology.SchemePreWeilTheory k F TateLine V dimension product fst snd point
        CH CHgrade cyclePullback cyclePushforward pointCycle H Picard)
      {X Z : V} (i : Z ⟶ X) (r : ℕ)
      [IsClosedImmersion (T.scheme.map i).left]
      (hcodim : TopologicalSpace.HasPureCodimension
        (Set.range (T.scheme.map i).left.base) r)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r
        (Scheme.Hom.conormalSheaf (T.scheme.map i).left)]
      (hK₀ : ∃ alpha : Scheme.K0 (T.scheme.obj X).left,
        Scheme.K0.pullback (T.scheme.map i).left alpha =
          Scheme.VectorBundleK0.toK0 (T.scheme.obj Z).left
            (ObjectProperty.GrothendieckGroup.of
              (SheafOfModules.IsFiniteLocallyFree :
                ObjectProperty (T.scheme.obj Z).left.Modules)
              ⟨Scheme.Hom.conormalSheaf (T.scheme.map i).left,
                Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r
                  (Scheme.Hom.conormalSheaf (T.scheme.map i).left)⟩))
      (a : H X) (ha : T.pullback i a = 0),
      T.cycleClass X (cyclePushforward i (1 : CHgrade Z 0)) * a = 0)
