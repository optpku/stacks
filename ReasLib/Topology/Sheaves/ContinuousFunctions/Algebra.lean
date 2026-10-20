/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Continuous functions as a sheaf of `R`-algebras

This file constructs the sheaf of continuous `R`-valued functions on a topological space as
a sheaf valued in `CommAlgCat R`, and the pullback (pushforward) map along continuous maps.

## API under `TopCat.ContinuousFunctions`

- `section'` — the `R`-algebra `C(U, R)` for an open `U`
- `presheaf` — the presheaf of continuous `R`-valued functions
- `sheaf` — the sheaf (presheaf + proof of sheaf condition)
- `pushforwardMap` — pullback along a continuous map `f : X → Y`
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v

namespace TopCat.ContinuousFunctions

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The `R`-algebra of continuous `R`-valued functions on an open subset. -/
abbrev section' (X : TopCat.{v}) (U : Opens X) : CommAlgCat.{max u v} R :=
  CommAlgCat.of R C(U, R)

/-- Restriction along an inclusion of opens. -/
def restriction (X : TopCat.{v}) {U V : Opens X} (i : V ⟶ U) :
    section' R X U ⟶ section' R X V :=
  CommAlgCat.ofHom <|
    ContinuousMap.compRightAlgHom R R (((Opens.toTopCat X).map i).hom)

/-- Restriction along the identity is the identity. -/
theorem restriction_id (X : TopCat.{v}) (U : Opens X) :
    restriction R X (𝟙 U) = 𝟙 _ := sorry

/-- Restriction is compatible with composition. -/
theorem restriction_comp (X : TopCat.{v})
    {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) :
    restriction R X (j ≫ i) = restriction R X i ≫ restriction R X j := sorry

/-- The presheaf `U ↦ C(U, R)` of continuous `R`-valued functions. -/
def presheaf (X : TopCat.{v}) : X.Presheaf (CommAlgCat.{max u v} R) where
  obj U := section' R X U.unop
  map i := restriction R X i.unop
  map_id U := restriction_id R X U.unop
  map_comp i j := restriction_comp R X i.unop j.unop

/-- The presheaf of continuous `R`-valued functions is a sheaf. -/
theorem presheaf_isSheaf (X : TopCat.{v}) : (presheaf R X).IsSheaf := sorry

/-- The sheaf of continuous `R`-valued functions. -/
abbrev sheaf (X : TopCat.{v}) : X.Sheaf (CommAlgCat.{max u v} R) :=
  ⟨presheaf R X, presheaf_isSheaf R X⟩

/-- The component of the pushforward map at one open. -/
def pushforwardMapApp {X Y : TopCat.{v}} (f : X ⟶ Y) (V : (Opens Y)ᵒᵖ) :
    (sheaf R Y).presheaf.obj V ⟶
      ((TopCat.Sheaf.pushforward (CommAlgCat.{max u v} R) f).obj (sheaf R X)).presheaf.obj V :=
  CommAlgCat.ofHom <|
    ContinuousMap.compRightAlgHom R R (f.hom.restrictPreimage (V.unop : Set Y))

/-- The pushforward map commutes with restriction. -/
theorem pushforwardMapApp_naturality {X Y : TopCat.{v}} (f : X ⟶ Y)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (sheaf R Y).presheaf.map i ≫ pushforwardMapApp R f V =
      pushforwardMapApp R f U ≫
        ((TopCat.Sheaf.pushforward (CommAlgCat.{max u v} R) f).obj (sheaf R X)).presheaf.map i := sorry

/-- The presheaf morphism pulling continuous functions back along `f`. -/
def presheafPushforwardMap {X Y : TopCat.{v}} (f : X ⟶ Y) :
    (sheaf R Y).presheaf ⟶
      ((TopCat.Sheaf.pushforward (CommAlgCat.{max u v} R) f).obj (sheaf R X)).presheaf where
  app := pushforwardMapApp R f
  naturality := fun {U V} i ↦ pushforwardMapApp_naturality R f (U := U) (V := V) i

/-- The sheaf morphism pulling continuous functions back along `f`. -/
def pushforwardMap {X Y : TopCat.{v}} (f : X ⟶ Y) :
    sheaf R Y ⟶ (TopCat.Sheaf.pushforward (CommAlgCat.{max u v} R) f).obj (sheaf R X) :=
  ObjectProperty.homMk (presheafPushforwardMap R f)

/-- The pushforward map at `V` is precomposition with the restriction of `f`. -/
theorem pushforwardMap_app {X Y : TopCat.{v}} (f : X ⟶ Y) (V : (Opens Y)ᵒᵖ) :
    (pushforwardMap R f).1.app V =
      CommAlgCat.ofHom
        (ContinuousMap.compRightAlgHom R R
          (f.hom.restrictPreimage (V.unop : Set Y))) := sorry

end TopCat.ContinuousFunctions

end

end
