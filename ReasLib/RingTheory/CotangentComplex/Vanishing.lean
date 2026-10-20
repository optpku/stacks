module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.RingTheory.CotangentComplex.DirectLimit
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Defs
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication

/-!
# Vanishing of cotangent complexes

Self-Tor independence and vanishing of the cotangent complex of tensor-square
multiplication imply vanishing of the original cotangent complex. The cotangent
complex also vanishes for weakly étale maps, flat epimorphisms, localizations,
flat unramified maps, étale maps, directed colimits of vanishing maps, and
(strict) henselizations of prime localizations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Algebra.CotangentComplex

/-- If `B` is Tor-independent of itself over `A` and the cotangent complex of
the canonical multiplication `B ⊗[A] B → B` vanishes in `D(B)`, then `L_{B/A}`
vanishes in `D(B)`. -/
@[stacks 08R1]
theorem derived_isZero_of_torIndependent_tensorSquare (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    (h_tor : ModuleCat.Tor.IsIndependent (ModuleCat.of A B) (ModuleCat.of A B))
    (h_zero : IsZero (DerivedCategory.Q.obj
      (RingHom.cotangentComplex (Algebra.tensorSquareMultiplication A B)))) :
    IsZero (derived A B) :=
  sorry

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` and `B ⊗[A] B → B` are flat, i.e., if `Algebra.WeaklyEtale A B`. -/
@[stacks 08R2]
theorem isZero_derived_of_weaklyEtale (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.WeaklyEtale A B) :
    IsZero (derived A B) :=
  sorry

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` is a flat epimorphism of rings. -/
@[stacks 08R2]
theorem isZero_derived_of_flat_isEpi (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h_flat : Module.Flat A B) (h_epi : Algebra.IsEpi A B) :
    IsZero (derived A B) :=
  sorry

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`B = S⁻¹A` for a multiplicative subset `S ⊆ A`. -/
@[stacks 08R2]
theorem isZero_derived_of_isLocalization (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] :
    IsZero (derived A B) :=
  sorry

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` is unramified and flat. -/
@[stacks 08R2]
theorem isZero_derived_of_unramified_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h_unramified : Algebra.Unramified A B) (h_flat : Module.Flat A B) :
    IsZero (derived A B) :=
  sorry

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if
`A → B` is étale. -/
@[stacks 08R2]
theorem isZero_derived_of_etale (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : Algebra.Etale A B) :
    IsZero (derived A B) :=
  sorry

/-- The cotangent complex of a filtered colimit of ring maps
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

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if `B`
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

/-- The cotangent complex `L_{B/A}` vanishes in `D(B)` if `B`
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
