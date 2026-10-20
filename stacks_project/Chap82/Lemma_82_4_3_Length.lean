/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length

/-!
# Length of an 𝒪_X-module at a point
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasLengthAt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (x : Points X) (d : ℕ∞), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasLengthAt_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (x : Points X) (d : ℕ∞),
    hasLengthAt F x d ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasLengthAt_of_lengthOnEtaleChart :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : X.Modules) {u : U.left} {x : Points X} {d : ℕ∞}
    (hu : Points.mapOfOver φ u = x) (hd : lengthOnEtaleChart φ F u = d),
    hasLengthAt F x d)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.hasFiniteNonzeroLengthAt_iff_hasLengthAt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (x : Points X),
    hasFiniteNonzeroLengthAt F x ↔ ∃ d : ℕ∞, 0 < d ∧ d < ⊤ ∧ hasLengthAt F x d)
