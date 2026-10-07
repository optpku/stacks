module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap30.Lemma_30_28_3_StageMap

/-!
# Algebraization of a compatible system of morphisms

A compatible system of morphisms between the adic stages of schemes over a
complete Noetherian affine base algebraizes uniquely when the source is proper
and the target is separated of finite type.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 30.28.3: if `A` is Noetherian and `I`-adically complete, `S = Spec(A)`,
`S_n = AdicThickening.spec I n`, `X` and `Y` are schemes over `S` with stages
`X_n = AdicThickening.stage fX I n` and `Y_n = AdicThickening.stage fY I n`, and a
compatible system of morphisms `g n : X_n ⟶ Y_n` over `S_n` is given, then whenever
`X ⟶ S` is proper and `Y ⟶ S` is separated of finite type there exists a unique
morphism `G : X ⟶ Y` over `S` whose base change to `S_n` is `g n`. -/
@[stacks 0A42]
theorem existsUnique_algebraizingHom
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A))
    [IsProper fX] [IsSeparated fY] [Scheme.Hom.FiniteType fY]
    (g : ∀ n : ℕ+, AdicThickening.stage fX I n ⟶ AdicThickening.stage fY I n)
    (h_over : ∀ n, g n ≫ AdicThickening.toSpec fY I n = AdicThickening.toSpec fX I n)
    (h_compat : ∀ n,
      g n ≫ AdicThickening.transition fY I n =
        AdicThickening.transition fX I n ≫ g (n + 1)) :
    ∃! G : X ⟶ Y, G ≫ fY = fX ∧
      ∀ n, g n ≫ AdicThickening.ι fY I n = AdicThickening.ι fX I n ≫ G :=
  sorry

/-- Two morphisms over `Spec(A)` that induce the same maps on every adic stage are equal,
when the source is proper and the target is separated of finite type over a complete
Noetherian affine base. -/
theorem hom_ext_of_forall_stageMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A))
    (fY : Y ⟶ Spec (CommRingCat.of A))
    [IsProper fX] [IsSeparated fY] [Scheme.Hom.FiniteType fY]
    {G₁ G₂ : X ⟶ Y} (h₁ : G₁ ≫ fY = fX) (h₂ : G₂ ≫ fY = fX)
    (h : ∀ n, AdicThickening.stageMap fX fY I G₁ h₁ n =
      AdicThickening.stageMap fX fY I G₂ h₂ n) :
    G₁ = G₂ :=
  sorry

end AlgebraicGeometry.Scheme
