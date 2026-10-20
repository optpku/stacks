/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ReasLib.RingTheory.LocalRing.Cotangent.Surjective

/-!
# Relative cotangent spaces of local algebras

For a local homomorphism of local rings `R → S`, the relative cotangent space of `S` over
`R` is the `ResidueField S`-vector space obtained by quotienting `CotangentSpace S` by the
residue span of `Ideal.map (algebraMap R S) (maximalIdeal R)`. This recovers
`maximalIdeal S ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) ⊔ maximalIdeal S ^ 2)`.
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace IsLocalRing

/-- The ideal `Ideal.map (algebraMap R S) (maximalIdeal R) ⊔ maximalIdeal S ^ 2`. -/
def relativeCotangentDenom (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] : Ideal S :=
  (maximalIdeal R).map (algebraMap R S) ⊔ maximalIdeal S ^ 2

noncomputable section

/-- The `ResidueField S`-span of the image of `Ideal.map (algebraMap R S) (maximalIdeal R)`
in `CotangentSpace S`. -/
def relativeCotangentSpan (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    Submodule (ResidueField S) (CotangentSpace S) :=
  Submodule.span (ResidueField S)
    (Set.range fun x : (maximalIdeal R).map (algebraMap R S) ↦
      (maximalIdeal S).toCotangent ⟨x.1, map_maximalIdeal_le (algebraMap R S) x.2⟩)

/-- The relative cotangent space of `S` over `R`, as a `ResidueField S`-vector space. -/
abbrev RelativeCotangentSpace (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] : Type v :=
  CotangentSpace S ⧸ relativeCotangentSpan R S

/-- The ideal `Ideal.map (algebraMap R S) (maximalIdeal R) ⊔ maximalIdeal S ^ 2`
is contained in `maximalIdeal S`. -/
theorem relativeCotangentDenom_le (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    relativeCotangentDenom R S ≤ maximalIdeal S := sorry

/-- If the base is a field, the relative span vanishes and the relative cotangent space
recovers `CotangentSpace S`. -/
theorem relativeCotangentSpan_eq_bot_of_isField (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hR : IsField R) : relativeCotangentSpan R S = ⊥ := sorry

namespace CotangentSpace

/-- The residue-field-semilinear map of cotangent spaces along a local algebra homomorphism. -/
def mapResidueField (S : Type v) (T : Type w) [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T] [Algebra S T] [IsLocalHom (algebraMap S T)] :
    CotangentSpace S →ₛₗ[ResidueField.map (algebraMap S T)] CotangentSpace T where
  toFun := map S T
  map_add' := (map S T).map_add
  map_smul' := sorry

/-- The residue-field-semilinear cotangent map agrees with `map` on values. -/
theorem mapResidueField_apply (S : Type v) (T : Type w) [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T] [Algebra S T] [IsLocalHom (algebraMap S T)]
    (x : CotangentSpace S) : mapResidueField S T x = map S T x := sorry

end CotangentSpace

/-- The relative span is compatible with the residue-field-semilinear cotangent map. -/
theorem relativeCotangentSpan_map_le (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T] [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap R T)] :
    relativeCotangentSpan R S ≤
      Submodule.comap (CotangentSpace.mapResidueField S T) (relativeCotangentSpan R T) := sorry

namespace RelativeCotangentSpace

/-- The class of an element of `maximalIdeal S` in the relative cotangent space. -/
def mk (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] (x : maximalIdeal S) :
    RelativeCotangentSpace R S :=
  Submodule.Quotient.mk ((maximalIdeal S).toCotangent x)

/-- The class of `x` vanishes if and only if `x` lies in the ideal
`Ideal.map (algebraMap R S) (maximalIdeal R) ⊔ maximalIdeal S ^ 2`. -/
theorem mk_eq_zero_iff (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (x : maximalIdeal S) :
    mk R S x = 0 ↔ (x : S) ∈ relativeCotangentDenom R S := sorry

/-- The map on relative cotangent spaces induced by a local homomorphism of `R`-algebras. -/
def map (R : Type u) (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap R T)] :
    RelativeCotangentSpace R S →ₛₗ[ResidueField.map (algebraMap S T)]
      RelativeCotangentSpace R T :=
  Submodule.mapQ (relativeCotangentSpan R S) (relativeCotangentSpan R T)
    (CotangentSpace.mapResidueField S T) (relativeCotangentSpan_map_le R S T)

/-- The induced map sends the class of an element of `maximalIdeal S` to the class of its
image in `maximalIdeal T`. -/
theorem map_mk (R : Type u) (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap R T)]
    (x : maximalIdeal S) :
    map R S T (mk R S x) =
      mk R T ⟨algebraMap S T x, (maximalIdeal_comap (algebraMap S T)).symm.le x.2⟩ := sorry

end RelativeCotangentSpace

end

end IsLocalRing
