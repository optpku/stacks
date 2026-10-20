/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Graph

/-!
# Lemma 99.12.1

If `X ⟶ B` is separated and `Z ⟶ B` is of finite presentation, flat, and
proper, the graph of a `T`-morphism `Z_T ⟶ X_T` defines a natural injective
transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}` of functors on `(Sch/B)^op`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

/- Lemma 99.12.1 (1): there is a natural transformation
Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B} sending a morphism f : Z_T ⟶ X_T over T
to the class of its graph Γ_f ⊂ (Z ×_B X)_T. -/
@[stacks 0D1A] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph :
  ∀ {S : Scheme.{u}} {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z],
    AlgebraicGeometry.AlgebraicSpace.RelativeHom.mor z x ⟶
      AlgebraicGeometry.AlgebraicSpace.RelativeHom.hilb z x)

/- Lemma 99.12.1 (2): the graph transformation is injective on every test scheme. -/
@[stacks 0D1A] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph_app_injective :
  ∀ {S : Scheme.{u}} {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z] (σ : SchemeOver B),
    Function.Injective fun b ↦
      (AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph z x).app (op σ) b)
