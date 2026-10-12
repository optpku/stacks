/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/- Lemma 59.48.4 (1) -/
@[stacks 04E4] #check
  (AlgebraicGeometry.exists_cover_factorization_of_closedImmersion_syntomic :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (𝒰 : X.Cover.{v} (precoverage @Syntomic)),
      ∃ 𝒱 : Y.Cover.{max u v} (precoverage @Syntomic),
        ∀ j : 𝒱.I₀,
          IsEmpty (pullback (𝒱.f j) f : Scheme.{u}) ∨
            ∃ i : 𝒰.I₀, ∃ m : (pullback (𝒱.f j) f : Scheme.{u}) ⟶ 𝒰.X i,
              pullback.snd (𝒱.f j) f = m ≫ 𝒰.f i)

/- Lemma 59.48.4 (2) -/
@[stacks 04E4] #check
  (AlgebraicGeometry.exists_cover_factorization_of_closedImmersion_smooth :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (𝒰 : X.Cover.{v} (precoverage @Smooth)),
      ∃ 𝒱 : Y.Cover.{max u v} (precoverage @Smooth),
        ∀ j : 𝒱.I₀,
          IsEmpty (pullback (𝒱.f j) f : Scheme.{u}) ∨
            ∃ i : 𝒰.I₀, ∃ m : (pullback (𝒱.f j) f : Scheme.{u}) ⟶ 𝒰.X i,
              pullback.snd (𝒱.f j) f = m ≫ 𝒰.f i)

/- Lemma 59.48.4 (3) -/
@[stacks 04E4] #check
  (AlgebraicGeometry.exists_cover_factorization_of_closedImmersion_etale :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (𝒰 : X.Cover.{v} (precoverage @Etale)),
      ∃ 𝒱 : Y.Cover.{max u v} (precoverage @Etale),
        ∀ j : 𝒱.I₀,
          IsEmpty (pullback (𝒱.f j) f : Scheme.{u}) ∨
            ∃ i : 𝒰.I₀, ∃ m : (pullback (𝒱.f j) f : Scheme.{u}) ⟶ 𝒰.X i,
              pullback.snd (𝒱.f j) f = m ≫ 𝒰.f i)

end AlgebraicGeometry
