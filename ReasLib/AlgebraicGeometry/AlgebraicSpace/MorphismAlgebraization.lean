/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdicThickening.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Algebraization of a compatible system of morphisms of algebraic spaces

A compatible system of morphisms between the adic stages of algebraic spaces over a
complete Noetherian affine base algebraizes when the source is proper and the
target is quasi-separated and locally of finite type. When the target is
separated of finite type, the algebraizing morphism is unique.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `A` is Noetherian and `I`-adically complete, `S = Spec(A)`,
`S_n = AdicThickening.spec I n`, `X` and `Y` are algebraic spaces over `S` with stages
`X_n = AdicThickening.stage X I n` and `Y_n = AdicThickening.stage Y I n`, and a
compatible system of morphisms `g n : X_n ⟶ Y_n` over `S_n` is given, then whenever
`X ⟶ S` is proper and `Y ⟶ S` is separated of finite type there exists a unique
morphism `G : X ⟶ Y` over `S` whose base change to `S_n` is `g n`. -/
theorem existsUnique_algebraizingHom
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase Y)]
    [FiniteType (SchemeRealization.toBase Y)]
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
    [Proper (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase Y)]
    [FiniteType (SchemeRealization.toBase Y)]
    {G₁ G₂ : X ⟶ Y}
    (h : ∀ n, AdicThickening.stageMap I G₁ n = AdicThickening.stageMap I G₂ n) :
    G₁ = G₂ :=
  sorry

/-- If `A` is Noetherian and `I`-adically complete, `S = Spec(A)`,
`S_n = AdicThickening.spec I n`, `X` and `Y` are algebraic spaces over `S` with stages
`X_n = AdicThickening.stage X I n` and `Y_n = AdicThickening.stage Y I n`, and a
compatible system of morphisms `g n : X_n ⟶ Y_n` over `S_n` is given, then whenever
`X ⟶ S` is proper and `Y ⟶ S` is quasi-separated and locally of finite type there
exists a morphism `G : X ⟶ Y` over `S` whose base change to `S_n` is `g n`.
Uniqueness is not claimed. -/
theorem exists_algebraizingHom_of_quasiSeparated
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)] [QuasiSeparated (SchemeRealization.toBase Y)]
    [LocallyOfFiniteType (SchemeRealization.toBase Y)]
    (g : ∀ n : ℕ+, AdicThickening.stage X I n ⟶ AdicThickening.stage Y I n)
    (h_over : ∀ n, g n ≫ AdicThickening.toSpec Y I n = AdicThickening.toSpec X I n)
    (h_compat : ∀ n,
      g n ≫ AdicThickening.transition Y I n =
        AdicThickening.transition X I n ≫ g (n + 1)) :
    ∃ G : X ⟶ Y, ∀ n, g n = AdicThickening.stageMap I G n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
