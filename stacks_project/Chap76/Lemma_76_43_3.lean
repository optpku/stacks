/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MorphismAlgebraization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 76.43.3: if `A` is Noetherian and `I`-adically complete, `S = Spec(A)`,
`S_n = AdicThickening.spec I n`, `X` and `Y` are algebraic spaces over `S` with stages
`X_n = AdicThickening.stage X I n` and `Y_n = AdicThickening.stage Y I n`, and a
compatible system of morphisms `g n : X_n ⟶ Y_n` over `S_n` is given, then whenever
`X ⟶ S` is proper and `Y ⟶ S` is separated of finite type there exists a unique
morphism `G : X ⟶ Y` over `S` whose base change to `S_n` is `g n`. -/
@[stacks 0A4Z] #check (AlgebraicGeometry.AlgebraicSpace.existsUnique_algebraizingHom :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase Y)]
    [FiniteType (SchemeRealization.toBase Y)]
    (g : ∀ n : ℕ+, AdicThickening.stage X I n ⟶ AdicThickening.stage Y I n)
    (h_over : ∀ n, g n ≫ AdicThickening.toSpec Y I n = AdicThickening.toSpec X I n)
    (h_compat : ∀ n,
      g n ≫ AdicThickening.transition Y I n =
        AdicThickening.transition X I n ≫ g (n + 1)),
    ∃! G : X ⟶ Y, ∀ n, g n = AdicThickening.stageMap I G n)

#check (AlgebraicGeometry.AlgebraicSpace.hom_ext_of_forall_stageMap :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase Y)]
    [FiniteType (SchemeRealization.toBase Y)]
    {G₁ G₂ : X ⟶ Y}
    (h : ∀ n, AdicThickening.stageMap I G₁ n = AdicThickening.stageMap I G₂ n),
    G₁ = G₂)
