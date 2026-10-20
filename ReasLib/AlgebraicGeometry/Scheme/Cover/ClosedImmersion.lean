/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Zariski
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe u v

namespace AlgebraicGeometry

/-- A syntomic morphism to a closed immersion is Zariski-locally induced by
syntomic morphisms over the ambient scheme. -/
theorem exists_zariskiCover_of_closedImmersion_syntomic
    {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (p : U ⟶ X) [Syntomic p] :
    ∃ (I : Type u) (V : I → Scheme.{u}) (g : ∀ i, V i ⟶ Y),
      (∀ i, Syntomic (g i)) ∧
        ∃ (h : ∀ i, (pullback (g i) f : Scheme.{u}) ⟶ U),
          (∀ i, pullback.snd (g i) f = h i ≫ p) ∧
            Presieve.ofArrows (fun i ↦ (pullback (g i) f : Scheme.{u})) h ∈
              Scheme.zariskiPrecoverage U := sorry

/-- A smooth morphism to a closed immersion is Zariski-locally induced by
smooth morphisms over the ambient scheme. -/
theorem exists_zariskiCover_of_closedImmersion_smooth
    {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (p : U ⟶ X) [Smooth p] :
    ∃ (I : Type u) (V : I → Scheme.{u}) (g : ∀ i, V i ⟶ Y),
      (∀ i, Smooth (g i)) ∧
        ∃ (h : ∀ i, (pullback (g i) f : Scheme.{u}) ⟶ U),
          (∀ i, pullback.snd (g i) f = h i ≫ p) ∧
            Presieve.ofArrows (fun i ↦ (pullback (g i) f : Scheme.{u})) h ∈
              Scheme.zariskiPrecoverage U := sorry

/-- An étale morphism to a closed immersion is Zariski-locally induced by
étale morphisms over the ambient scheme. -/
theorem exists_zariskiCover_of_closedImmersion_etale
    {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (p : U ⟶ X) [Etale p] :
    ∃ (I : Type v) (V : I → Scheme.{u}) (g : ∀ i, V i ⟶ Y),
      (∀ i, Etale (g i)) ∧
        ∃ (h : ∀ i, (pullback (g i) f : Scheme.{u}) ⟶ U),
          (∀ i, pullback.snd (g i) f = h i ≫ p) ∧
            Presieve.ofArrows (fun i ↦ (pullback (g i) f : Scheme.{u})) h ∈
              Scheme.zariskiPrecoverage U := sorry

/-- A syntomic cover of a closed subscheme extends to a syntomic cover of the
ambient scheme whose pullback components are empty or factor through the
given cover. -/
theorem exists_cover_factorization_of_closedImmersion_syntomic
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (𝒰 : X.Cover.{v} (precoverage @Syntomic)) :
    ∃ 𝒱 : Y.Cover.{max u v} (precoverage @Syntomic),
      ∀ j : 𝒱.I₀,
        IsEmpty (pullback (𝒱.f j) f : Scheme.{u}) ∨
          ∃ i : 𝒰.I₀, ∃ m : (pullback (𝒱.f j) f : Scheme.{u}) ⟶ 𝒰.X i,
            pullback.snd (𝒱.f j) f = m ≫ 𝒰.f i := sorry

/-- A smooth cover of a closed subscheme extends to a smooth cover of the
ambient scheme whose pullback components are empty or factor through the
given cover. -/
theorem exists_cover_factorization_of_closedImmersion_smooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (𝒰 : X.Cover.{v} (precoverage @Smooth)) :
    ∃ 𝒱 : Y.Cover.{max u v} (precoverage @Smooth),
      ∀ j : 𝒱.I₀,
        IsEmpty (pullback (𝒱.f j) f : Scheme.{u}) ∨
          ∃ i : 𝒰.I₀, ∃ m : (pullback (𝒱.f j) f : Scheme.{u}) ⟶ 𝒰.X i,
            pullback.snd (𝒱.f j) f = m ≫ 𝒰.f i := sorry

/-- An étale cover of a closed subscheme extends to an étale cover of the
ambient scheme whose pullback components are empty or factor through the
given cover. -/
theorem exists_cover_factorization_of_closedImmersion_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (𝒰 : X.Cover.{v} (precoverage @Etale)) :
    ∃ 𝒱 : Y.Cover.{max u v} (precoverage @Etale),
      ∀ j : 𝒱.I₀,
        IsEmpty (pullback (𝒱.f j) f : Scheme.{u}) ∨
          ∃ i : 𝒰.I₀, ∃ m : (pullback (𝒱.f j) f : Scheme.{u}) ⟶ 𝒰.X i,
            pullback.snd (𝒱.f j) f = m ≫ 𝒰.f i := sorry

end AlgebraicGeometry
