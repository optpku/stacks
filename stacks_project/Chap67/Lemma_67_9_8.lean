/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Descent
import StacksCheckRecall

/-!
# Descent of separation along a universally closed surjection

A surjective universally closed morphism of algebraic spaces sends a
quasi-separated (resp. separated) source to a quasi-separated (resp.
separated) target, both absolutely and relatively over a base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.9.8: a surjective universally closed morphism descends absolute
quasi-separatedness and separatedness, and both properties relative to any
algebraic-space base. -/
@[stacks 05Z2] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.of_surjective_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [Surjective f] → [UniversallyClosed f] → [IsAbsolutelyQuasiSeparated X] →
      IsAbsolutelyQuasiSeparated Y)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated.of_surjective_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [Surjective f] → [UniversallyClosed f] → [IsAbsolutelySeparated X] →
      IsAbsolutelySeparated Y)

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiSeparated.of_comp_surjective_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B),
      [Surjective f] → [UniversallyClosed f] → [QuasiSeparated (f ≫ g)] → QuasiSeparated g)

#check
  (AlgebraicGeometry.AlgebraicSpace.Separated.of_comp_surjective_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ B),
      [Surjective f] → [UniversallyClosed f] → [Separated (f ≫ g)] → Separated g)
