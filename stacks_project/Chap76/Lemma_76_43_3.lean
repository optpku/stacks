/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap76.Lemma_76_43_1_AdicThickening
public import stacks_project.Chap76.Lemma_76_43_3_StageMap

/-!
# Algebraization of a compatible system of morphisms of algebraic spaces

A compatible system of morphisms between the adic stages of algebraic spaces over a
complete Noetherian affine base algebraizes uniquely when the source is proper
and the target is separated of finite type.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.43.3: if `A` is Noetherian and `I`-adically complete, `S = Spec(A)`,
`S_n = AdicThickening.spec I n`, `X` and `Y` are algebraic spaces over `S` with stages
`X_n = AdicThickening.stage X I n` and `Y_n = AdicThickening.stage Y I n`, and a
compatible system of morphisms `g n : X_n ⟶ Y_n` over `S_n` is given, then whenever
`X ⟶ S` is proper and `Y ⟶ S` is separated of finite type there exists a unique
morphism `G : X ⟶ Y` over `S` whose base change to `S_n` is `g n`. -/
@[stacks 0A4Z]
theorem existsUnique_algebraizingHom
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (toBase X)] [Separated (toBase Y)] [FiniteType (toBase Y)]
    (g : ∀ n : ℕ+, AdicThickening.stage X I n ⟶ AdicThickening.stage Y I n)
    (h_over : ∀ n, g n ≫ AdicThickening.toSpec Y I n = AdicThickening.toSpec X I n)
    (h_compat : ∀ n,
      g n ≫ AdicThickening.transition Y I n =
        AdicThickening.transition X I n ≫ g (n + 1)) :
    ∃! G : X ⟶ Y, ∀ n, g n = AdicThickening.stageMap I G n :=
  sorry

/-- Two morphisms of algebraic spaces over `Spec(A)` that induce the same maps on every
adic stage are equal, when the source is proper and the target is separated of finite
type over a complete Noetherian affine base. -/
theorem hom_ext_of_forall_stageMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (toBase X)] [Separated (toBase Y)] [FiniteType (toBase Y)]
    {G₁ G₂ : X ⟶ Y}
    (h : ∀ n, AdicThickening.stageMap I G₁ n = AdicThickening.stageMap I G₂ n) :
    G₁ = G₂ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
