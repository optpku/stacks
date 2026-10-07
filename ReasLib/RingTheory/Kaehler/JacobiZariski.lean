module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobi-Zariski consequences for Kähler differentials

This leaf records reusable consequences of the Jacobi-Zariski sequence for a
tower of commutative algebras.

@stack 06A7
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.H1Cotangent

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Tag `00S2`: if the first cotangent homology of `T / S` is subsingleton,
then its Jacobi-Zariski connecting map over `R` vanishes. -/
@[stacks 00S2 "Jacobi-Zariski connecting map vanishes"]
theorem delta_eq_zero_of_subsingleton
    (hH1 : Subsingleton (H1Cotangent S T)) :
    δ R S T = 0 := sorry

/-- Tag `00S2`: if the first cotangent homology of `T / R` is subsingleton,
then the next Jacobi-Zariski connecting map is injective. -/
@[stacks 00S2 "Jacobi-Zariski connecting map injectivity"]
theorem delta_injective_of_subsingleton
    (hH1 : Subsingleton (H1Cotangent R T)) :
    Function.Injective (δ R S T) := sorry

/-- Tag `00S2`: vanishing first cotangent homology makes the left
Jacobi-Zariski Kähler base-change map injective.  The vanishing hypothesis is
an explicit proposition so callers do not need a temporary instance. -/
@[stacks 00S2 "Jacobi-Zariski base-change injectivity"]
theorem mapBaseChange_injective_of_subsingleton
    (hH1 : Subsingleton (H1Cotangent S T)) :
    Function.Injective (KaehlerDifferential.mapBaseChange R S T) := sorry

/-- Tag `00S2`: injectivity of the Kähler base-change map makes its preceding
Jacobi-Zariski connecting map zero. -/
@[stacks 00S2 "Jacobi-Zariski connecting map vanishes by injectivity"]
theorem delta_eq_zero_of_mapBaseChange_injective
    (hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) :
    δ R S T = 0 := sorry

/-- Tag `00S2`: if first cotangent homology vanishes over `R` and the Kähler
base-change map is injective, then first cotangent homology vanishes over `S`. -/
@[stacks 00S2 "Jacobi-Zariski cotangent homology vanishing"]
theorem subsingleton_of_mapBaseChange_injective
    (hH1 : Subsingleton (H1Cotangent R T))
    (hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton (H1Cotangent S T) := sorry

/-- Tag `00S2`: injectivity of the Kähler base-change map makes the preceding
first-cotangent-homology comparison map surjective. -/
@[stacks 00S2 "Jacobi-Zariski cotangent homology surjectivity"]
theorem map_surjective_of_mapBaseChange_injective
    (hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) :
    Function.Surjective (map R S T T) := sorry

/-- Tag `065V`: when the outside map of an algebra tower is surjective, the
Jacobi-Zariski connecting map on first cotangent homology is surjective. -/
@[stacks 065V "surjective Jacobi-Zariski connecting map"]
theorem delta_surjective_of_algebraMap_surjective
    (hRT : Function.Surjective (algebraMap R T)) :
    Function.Surjective (δ R S T) := sorry

/-- Lemma 10.138.11, tag `06A7`: formal smoothness and a surjective outside
map make the Jacobi-Zariski connecting map admit a linear section. -/
@[stacks 06A7]
theorem delta_has_section_of_formallySmooth
    [Algebra.FormallySmooth R S]
    (hRT : Function.Surjective (algebraMap R T)) :
    ∃ σ : T ⊗[S] Ω[S⁄R] →ₗ[T] H1Cotangent S T,
      (δ R S T).comp σ = LinearMap.id := sorry

end Algebra.H1Cotangent

namespace KaehlerDifferential

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Tag `031K`: a projective target of the transitivity map admits a linear
section. -/
@[stacks 031K "Kahler transitivity section"]
theorem map_has_section_of_projective
    [Module.Projective T Ω[T⁄S]] :
    ∃ s : Ω[T⁄S] →ₗ[T] Ω[T⁄R],
      (map R S T T).comp s = LinearMap.id := sorry

/-- Lemma 10.138.10, tag `06A6`: if `R → T` is formally smooth and
`S → T` is surjective, then the Kähler base-change map has a linear section. -/
@[stacks 06A6]
theorem mapBaseChange_has_section_of_formallySmooth
    [Algebra.FormallySmooth R T]
    (hST : Function.Surjective (algebraMap S T)) :
    ∃ σ : Ω[T⁄R] →ₗ[T] T ⊗[S] Ω[S⁄R],
      (mapBaseChange R S T).comp σ = LinearMap.id := sorry

/-- Lemma 10.138.9, tag `031K`: formal smoothness of `S → T` splits the
Kähler-differential transitivity sequence over every base ring `R`. -/
@[stacks 031K]
theorem transitivity_sequence_splits_of_formallySmooth
    [Algebra.FormallySmooth S T] :
    Function.Injective (mapBaseChange R S T) ∧
      ∃ s : Ω[T⁄S] →ₗ[T] Ω[T⁄R],
        (map R S T T).comp s = LinearMap.id := sorry

end KaehlerDifferential
