/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import stacks_project.Chap30.Lemma_30_28_1_AdicThickening

/-!
# Grothendieck's algebraization theorem

A cartesian successor ladder of schemes over the adic spectra of a complete
Noetherian ring, equipped with compatible invertible sheaves whose first stage
is proper with an ample invertible sheaf, algebraizes to a proper morphism
with an ample invertible sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Compatibility of restriction isomorphisms `ψ n : (Modules.pullback (e n)).obj M ≅ L n`
with the given transition isomorphisms `φ n` along a cone `e n = succ n ≫ e (n + 1)`. -/
def sheafIsoCompatible {X : ℕ+ → Scheme.{u}} {W : Scheme.{u}}
    (succ : ∀ n, X n ⟶ X (n + 1)) (L : ∀ n, (X n).Modules)
    (φ : ∀ n, (Modules.pullback (succ n)).obj (L (n + 1)) ≅ L n)
    (M : W.Modules) (e : ∀ n, X n ⟶ W)
    (he : ∀ n, e n = succ n ≫ e (n + 1))
    (ψ : ∀ n, (Modules.pullback (e n)).obj M ≅ L n) : Prop :=
  ∀ n, (Modules.pullback (succ n)).mapIso (ψ (n + 1)) ≪≫ φ n =
    (Modules.pullbackComp (succ n) (e (n + 1))).app M ≪≫
      (Modules.pullbackCongr (he n).symm).app M ≪≫ ψ n

/-- `sheafIsoCompatible` is the iso-level naturality equation for restriction along the cone. -/
theorem sheafIsoCompatible_iff {X : ℕ+ → Scheme.{u}} {W : Scheme.{u}}
    (succ : ∀ n, X n ⟶ X (n + 1)) (L : ∀ n, (X n).Modules)
    (φ : ∀ n, (Modules.pullback (succ n)).obj (L (n + 1)) ≅ L n)
    (M : W.Modules) (e : ∀ n, X n ⟶ W)
    (he : ∀ n, e n = succ n ≫ e (n + 1))
    (ψ : ∀ n, (Modules.pullback (e n)).obj M ≅ L n) :
    sheafIsoCompatible succ L φ M e he ψ ↔
      ∀ n, (Modules.pullback (succ n)).mapIso (ψ (n + 1)) ≪≫ φ n =
        (Modules.pullbackComp (succ n) (e (n + 1))).app M ≪≫
          (Modules.pullbackCongr (he n).symm).app M ≪≫ ψ n :=
  sorry

/-- Theorem 30.28.4 (Grothendieck's algebraization theorem): if `A` is Noetherian and
`I`-adically complete, `S = Spec(A)`, `S_n = AdicThickening.spec I n`, a cartesian
successor ladder of schemes `X n` over `S_n` is given together with invertible
sheaves `L n` and isomorphisms `φ n : (Modules.pullback (succ n)).obj (L (n + 1)) ≅ L n`,
and if `X 1 ⟶ S_1` is proper with `L 1` ample on `X 1`, then there exist a proper
morphism `W ⟶ S`, an ample invertible `𝒪_W`-module `M`, comparison maps identifying
each `X n` with `W ×_S S_n`, and sheaf isomorphisms `L n ≅ M|_{X n}` compatible
with `succ n` and `φ n`. -/
@[stacks 089A]
theorem exists_algebraizingProperAmple
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : ℕ+ → Scheme.{u}) (succ : ∀ n, X n ⟶ X (n + 1))
    (toSpec : ∀ n, X n ⟶ AdicThickening.spec I n)
    (h_pb : ∀ n,
      IsPullback (succ n) (toSpec n) (toSpec (n + 1)) (AdicThickening.specTransition I n))
    (L : ∀ n, (X n).Modules) [∀ n, Modules.Invertible (L n)]
    (φ : ∀ n, (Modules.pullback (succ n)).obj (L (n + 1)) ≅ L n)
    [IsProper (toSpec 1)] [Modules.IsAmple (L 1)] :
    ∃ (W : Scheme.{u}) (π : W ⟶ Spec (CommRingCat.of A)) (M : W.Modules)
      (hM : Modules.Invertible M) (e : ∀ n, X n ⟶ W)
      (he : ∀ n, e n = succ n ≫ e (n + 1))
      (ψ : ∀ n, (Modules.pullback (e n)).obj M ≅ L n),
      IsProper π ∧ @Modules.IsAmple W M hM ∧
        (∀ n, IsPullback (e n) (toSpec n) π (AdicThickening.toAmbient I n)) ∧
          sheafIsoCompatible succ L φ M e he ψ :=
  sorry

end AlgebraicGeometry.Scheme
