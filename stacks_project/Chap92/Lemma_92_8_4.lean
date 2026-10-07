module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Defs
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of the cotangent complex

The André-Quillen complex `L_{B/A}` vanishes in `D(B)` for weakly étale maps,
flat epimorphisms, localizations, unramified flat maps, étale maps, filtered
colimits of vanishing maps, and (strict) henselizations of local rings of `A`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.8.4 (1). The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` and `B ⊗[A] B → B` are flat, i.e., if `Algebra.WeaklyEtale A B`. -/
@[stacks 08R2]
theorem isZero_derived_of_weaklyEtale (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.WeaklyEtale A B) :
    IsZero (derived A B) :=
  sorry

/-- Lemma 92.8.4 (2). The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` is a flat epimorphism of rings. -/
@[stacks 08R2]
theorem isZero_derived_of_flat_isEpi (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h_flat : Module.Flat A B) (h_epi : Algebra.IsEpi A B) :
    IsZero (derived A B) :=
  sorry

/-- Lemma 92.8.4 (3). The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`B = S⁻¹A` for a multiplicative subset `S ⊆ A`. -/
@[stacks 08R2]
theorem isZero_derived_of_isLocalization (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] :
    IsZero (derived A B) :=
  sorry

/-- Lemma 92.8.4 (4). The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` is unramified and flat. -/
@[stacks 08R2]
theorem isZero_derived_of_unramified_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h_unramified : Algebra.Unramified A B) (h_flat : Module.Flat A B) :
    IsZero (derived A B) :=
  sorry

/-- Lemma 92.8.4 (5). The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` is étale. -/
@[stacks 08R2]
theorem isZero_derived_of_etale (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale A B) :
    IsZero (derived A B) :=
  sorry

/-- Lemma 92.8.4 (6). The cotangent complex of a filtered colimit of ring maps
vanishes in the derived category of the colimit if each stagewise cotangent
complex `L_{S i / R i}` vanishes. -/
@[stacks 08R2]
theorem isZero_derived_of_directLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {R S : I → Type u}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    (ρ : ∀ i j, i ≤ j → R i →+* R j) (σ : ∀ i j, i ≤ j → S i →+* S j)
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (h_zero : ∀ i, IsZero (derived (R i) (S i))) :
    IsZero (DerivedCategory.Q.obj (DirectLimit.targetComplex ρ σ hcomm)) :=
  sorry

/-- Lemma 92.8.4 (7). The cotangent complex `L_{B/A}` vanishes in `D(B)` if `B`
is a henselization of a local ring of `A`. -/
@[stacks 08R2]
theorem isZero_derived_of_isHenselizationOf_atPrime
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime]
    [Algebra (Localization.AtPrime p) B]
    [IsScalarTower A (Localization.AtPrime p) B]
    (h : IsHenselizationOf (Localization.AtPrime p) B) :
    IsZero (derived A B) :=
  sorry

/-- Lemma 92.8.4 (8). The cotangent complex `L_{B/A}` vanishes in `D(B)` if `B`
is a strict henselization of a local ring of `A`. -/
@[stacks 08R2]
theorem isZero_derived_of_isStrictHenselizationOf_atPrime
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime]
    [Algebra (Localization.AtPrime p) B]
    [IsScalarTower A (Localization.AtPrime p) B]
    (h : IsStrictHenselizationOf (Localization.AtPrime p) B) :
    IsZero (derived A B) :=
  sorry

end Algebra.CotangentComplex
