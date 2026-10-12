/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_23_1_Smooth
public import stacks_project.Chap90.Lemma_90_8_6_Coyoneda
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries

/-!
# Smoothness of restricted coyoneda maps

A morphism in `CompleteLocalAlgCat Λ k` induces a smooth map of restricted coyoneda
functors on `ArtinianLocalAlgCat` if and only if the target is a finite-variable
power series ring over the source.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- Lemma 90.8.6: for a morphism `f : R ⟶ S` in `CompleteLocalAlgCat Λ k`, the induced
morphism `restrictedCoyoneda S ⟶ restrictedCoyoneda R` is smooth if and only if `S`
is a finite-variable power series ring over `R` along `f`. -/
@[stacks 06HL]
theorem restrictedCoyonedaMap_isSmooth_iff {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    NatTrans.IsSmooth (restrictedCoyonedaMap f) ↔ IsPowerSeriesOver f :=
  sorry

end CompleteLocalAlgCat
