/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.TheoremOfCube
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.33.7: let `f : X ⟶ S` and `g : Y ⟶ S` be flat, proper, finitely
presented morphisms satisfying the structure-sheaf base-change hypotheses of
Lemma 37.33.1, with chosen sections `σ` and `τ`. An invertible module on
`pullback f g` that is trivial along `1 × τ`, along `σ × 1`, and on the fiber
over `s` is trivial over the inverse image of some open neighborhood of `s`. -/
@[stacks 0BF3] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.isTrivial_near_of_sections_and_fiber :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
      [AlgebraicGeometry.Flat g] [AlgebraicGeometry.IsProper g]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation g]
      (h_unit_f : ∀ {T : AlgebraicGeometry.Scheme.{u}} (h : T ⟶ S),
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          (pullback.snd f h).toRingCatSheafHom))
      (h_unit_g : ∀ {T : AlgebraicGeometry.Scheme.{u}} (h : T ⟶ S),
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          (pullback.snd g h).toRingCatSheafHom))
      (σ : SplitEpi f) (τ : SplitEpi g) (s : S)
      (L : (pullback f g).Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (h_trivial_fst : AlgebraicGeometry.RingedSpace.IsTrivial
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (τ.pullbackFst f).section_).obj L))
      (h_trivial_snd : AlgebraicGeometry.RingedSpace.IsTrivial
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (σ.pullbackSnd g).section_).obj L))
      (h_trivial_fiber : AlgebraicGeometry.RingedSpace.IsTrivial
        ((AlgebraicGeometry.Scheme.Modules.pullback
          ((pullback.fst f g ≫ f).fiberι s)).obj L)),
      ∃ U : S.Opens, s ∈ U ∧ AlgebraicGeometry.RingedSpace.IsTrivial
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.fst (pullback.fst f g ≫ f) U.ι)).obj L))
