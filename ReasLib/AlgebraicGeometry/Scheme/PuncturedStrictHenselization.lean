/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.PuncturedSpectrum

universe u v

namespace AlgebraicGeometry.Scheme.PuncturedStrictHenselization

/-- The punctured spectrum of a strict henselization maps into the complement of a closed point. -/
theorem range_subset {X : Scheme.{u}} {ι : Type v} (x : ι → X)
    (hx : ∀ i, IsClosed ({x i} : Set X)) (U : X.Opens)
    (hUeq : (U : Set X) = (Set.range x)ᶜ) (Ash : ι → Type u)
    [∀ i, CommRing (Ash i)]
    [∀ i, Algebra (X.presheaf.stalk (x i)) (Ash i)]
    [∀ i, IsStrictHenselizationOf (X.presheaf.stalk (x i)) (Ash i)] (i : ι) :
    Set.range
        (((puncturedOpen (Ash i)).ι ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap (X.presheaf.stalk (x i)) (Ash i))) ≫
            X.fromSpecStalk (x i)).base) ⊆
      Set.range U.ι.base := sorry

/-- The canonical morphism from a punctured strict henselization to the chosen complement. -/
noncomputable def map {X : Scheme.{u}} {ι : Type v} (x : ι → X)
    (hx : ∀ i, IsClosed ({x i} : Set X)) (U : X.Opens)
    (hUeq : (U : Set X) = (Set.range x)ᶜ) (Ash : ι → Type u)
    [∀ i, CommRing (Ash i)]
    [∀ i, Algebra (X.presheaf.stalk (x i)) (Ash i)]
    [∀ i, IsStrictHenselizationOf (X.presheaf.stalk (x i)) (Ash i)] (i : ι) :
    PuncturedSpectrum.scheme (Ash i) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι
    ((puncturedOpen (Ash i)).ι ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk (x i)) (Ash i))) ≫
      X.fromSpecStalk (x i))
    (range_subset x hx U hUeq Ash i)

/-- Composition with the open immersion recovers the punctured strict henselization map. -/
theorem map_ι {X : Scheme.{u}} {ι : Type v} (x : ι → X)
    (hx : ∀ i, IsClosed ({x i} : Set X)) (U : X.Opens)
    (hUeq : (U : Set X) = (Set.range x)ᶜ) (Ash : ι → Type u)
    [∀ i, CommRing (Ash i)]
    [∀ i, Algebra (X.presheaf.stalk (x i)) (Ash i)]
    [∀ i, IsStrictHenselizationOf (X.presheaf.stalk (x i)) (Ash i)] (i : ι) :
    map x hx U hUeq Ash i ≫ U.ι =
      (puncturedOpen (Ash i)).ι ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk (x i)) (Ash i))) ≫
        X.fromSpecStalk (x i) := sorry

end AlgebraicGeometry.Scheme.PuncturedStrictHenselization
