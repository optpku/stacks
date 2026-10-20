module

public import ReasLib.RingTheory.Algebra.TensorProduct.Fiber
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.LocalRing.Unibranch
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalization after strict Henselization

For a local ring `A` and a strict Henselization `Ash`, this leaf records the fiber and generic-point
geometry of `Unibranch.normalization A ⊗[A] Ash`. The fiber classifier is concrete: an embedding of
the normalization residue field determines the kernel of an explicit tensor-product evaluation
map. Only its bijectivity and the prime-incidence conclusions remain proof obligations.

@stack 0C25
-/

@[expose] public section

open Ideal IsLocalRing
open scoped TensorProduct Unibranch

universe u v w

noncomputable section

namespace Unibranch.StrictHenselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ash : Type v} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- The base change of the normalization of `A_red` to a strict Henselization of `A`. -/
@[stacks 0C25 "normalization base change"]
abbrev normalizationBaseChange := Unibranch.normalization A ⊗[A] Ash

/-- The canonical map from the normalization into its strict-Henselization base change. -/
@[stacks 0C25 "left normalization map"]
abbrev normalizationMap :
    Unibranch.normalization A →+* normalizationBaseChange (A := A) (Ash := Ash) :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The canonical map from the strict Henselization into the normalization base change. -/
@[stacks 0C25 "right strict-Henselization map"]
abbrev strictHenselizationMap :
    Ash →+* normalizationBaseChange (A := A) (Ash := Ash) :=
  (Algebra.TensorProduct.includeRight :
    Ash →ₐ[A] normalizationBaseChange (A := A) (Ash := Ash)).toRingHom

/-- Lemma 15.107.4 (1), Stacks `0C25`: the residue field at a maximal point of the normalization
is algebraic over the residue field of `A`. -/
@[stacks 0C25 "(1), algebraic normalization residue field"]
theorem residueField_isAlgebraic (m : MaximalSpectrum (Unibranch.normalization A)) :
    Algebra.IsAlgebraic (ResidueField A) m.asIdeal.ResidueField := sorry

section Fiber

variable {Kbar : Type w} [Field Kbar] [Algebra (ResidueField A) Kbar]
  [IsAlgClosure (ResidueField A) Kbar]

/-- The structural map from `A` to the chosen algebraic closure of its residue field. -/
@[stacks 0C25 "base map to the algebraic closure"]
noncomputable def baseToAlgebraicClosure : A →+* Kbar :=
  (algebraMap (ResidueField A) Kbar).comp (IsLocalRing.residue A)

/-- The normalization-residue embedding used by the fiber evaluation respects the map from `A`. -/
@[stacks 0C25 "normalization-residue compatibility"]
theorem fiberEvaluation_left_commutes
    (m : MaximalSpectrum (Unibranch.normalization A))
    (σ : m.asIdeal.ResidueField →ₐ[ResidueField A] Kbar) (a : A) :
    σ (algebraMap A m.asIdeal.ResidueField a) =
      baseToAlgebraicClosure (A := A) (Kbar := Kbar) a := sorry

/-- The strict-Henselization residue embedding used by the fiber evaluation respects the map
from `A`. -/
@[stacks 0C25 "strict-Henselization residue compatibility"]
theorem fiberEvaluation_right_commutes
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar) (a : A) :
    τ (IsLocalRing.residue Ash (algebraMap A Ash a)) =
      baseToAlgebraicClosure (A := A) (Kbar := Kbar) a := sorry

/-- The tensor-product evaluation whose kernel is the fiber point associated to `σ`. -/
@[stacks 0C25 "fiber evaluation map"]
noncomputable def fiberEvaluation
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar)
    (m : MaximalSpectrum (Unibranch.normalization A))
    (σ : m.asIdeal.ResidueField →ₐ[ResidueField A] Kbar) :
    m.asIdeal.Fiber (normalizationBaseChange (A := A) (Ash := Ash)) →+* Kbar :=
  letI : Algebra A Kbar :=
    (baseToAlgebraicClosure (A := A) (Kbar := Kbar)).toAlgebra
  let left : m.asIdeal.ResidueField →ₐ[A] Kbar :=
    { toRingHom := σ.toRingHom
      commutes' := fiberEvaluation_left_commutes m σ }
  let right : Ash →ₐ[A] Kbar :=
    { toRingHom := τ.toRingHom.comp (IsLocalRing.residue Ash)
      commutes' := fiberEvaluation_right_commutes τ }
  (Algebra.TensorProduct.lift left right (fun _ _ ↦ Commute.all _ _)).toRingHom.comp
    (Algebra.TensorProduct.fiberRightAlgEquiv
      (R := A) (S := Ash) (R' := Unibranch.normalization A) m.toPrimeSpectrum).toRingEquiv.toRingHom

/-- On the tensor model of the fiber, `fiberEvaluation` is the product of the two chosen residue
embeddings. -/
@[stacks 0C25 "fiber evaluation formula"]
theorem fiberEvaluation_tmul
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar)
    (m : MaximalSpectrum (Unibranch.normalization A))
    (σ : m.asIdeal.ResidueField →ₐ[ResidueField A] Kbar)
    (x : m.asIdeal.ResidueField) (y : Ash) :
    fiberEvaluation τ m σ
        ((Algebra.TensorProduct.fiberRightAlgEquiv
          (R := A) (S := Ash) (R' := Unibranch.normalization A) m.toPrimeSpectrum).symm
          (x ⊗ₜ[A] y)) =
      σ x * τ (IsLocalRing.residue Ash y) := sorry

/-- The fiber point associated to a residue-field embedding is the kernel of its explicit tensor
evaluation map. -/
@[stacks 0C25 "fiber point attached to a residue embedding"]
noncomputable def fiberPoint
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar)
    (m : MaximalSpectrum (Unibranch.normalization A))
    (σ : m.asIdeal.ResidueField →ₐ[ResidueField A] Kbar) :
    PrimeSpectrum (m.asIdeal.Fiber (normalizationBaseChange (A := A) (Ash := Ash))) :=
  ⟨RingHom.ker (fiberEvaluation τ m σ), RingHom.ker_isPrime _⟩

/-- The ideal underlying `fiberPoint` is the kernel of `fiberEvaluation`. -/
@[stacks 0C25 "fiber point kernel"]
theorem fiberPoint_asIdeal
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar)
    (m : MaximalSpectrum (Unibranch.normalization A))
    (σ : m.asIdeal.ResidueField →ₐ[ResidueField A] Kbar) :
    (fiberPoint τ m σ).asIdeal = RingHom.ker (fiberEvaluation τ m σ) := sorry

/-- Lemma 15.107.4 (2), Stacks `0C25`: residue-field embeddings classify the points of the
fiber over a maximal point of the normalization. -/
@[stacks 0C25 "(2), fiber points and residue embeddings"]
theorem fiberPoint_bijective
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar)
    (m : MaximalSpectrum (Unibranch.normalization A)) :
    Function.Bijective (fiberPoint τ m) := sorry

/-- Equivalence form of the fiber-point classification in Lemma 15.107.4 (2). -/
@[stacks 0C25 "(2), fiber-point equivalence"]
noncomputable def fiberEquiv
    (τ : ResidueField Ash →ₐ[ResidueField A] Kbar)
    (m : MaximalSpectrum (Unibranch.normalization A)) :
    (m.asIdeal.ResidueField →ₐ[ResidueField A] Kbar) ≃
      PrimeSpectrum (m.asIdeal.Fiber (normalizationBaseChange (A := A) (Ash := Ash))) :=
  Equiv.ofBijective (fiberPoint τ m) (fiberPoint_bijective τ m)

end Fiber

/-- Lemma 15.107.4 (3), Stacks `0C25`: contraction along the right structural map is a bijection
on minimal primes. -/
@[stacks 0C25 "(3), minimal primes"]
theorem minimalPrimes_bijOn (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn (Ideal.comap (strictHenselizationMap (A := A) (Ash := Ash)))
      (minimalPrimes (normalizationBaseChange (A := A) (Ash := Ash)))
      (minimalPrimes Ash) := sorry

/-- Lemma 15.107.4 (4), Stacks `0C25`: every minimal prime of the normalization base change lies
in a unique maximal ideal. -/
@[stacks 0C25 "(4), unique maximal ideal above a minimal prime"]
theorem minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal (normalizationBaseChange (A := A) (Ash := Ash))}
    (hp : p ∈ minimalPrimes (normalizationBaseChange (A := A) (Ash := Ash))) :
    ∃! m : Ideal (normalizationBaseChange (A := A) (Ash := Ash)),
      m.IsMaximal ∧ p ≤ m := sorry

/-- Lemma 15.107.4 (5), Stacks `0C25`: every maximal ideal of the normalization base change
contains a unique minimal prime. -/
@[stacks 0C25 "(5), unique minimal prime below a maximal ideal"]
theorem maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal (normalizationBaseChange (A := A) (Ash := Ash))} (hm : m.IsMaximal) :
    ∃! p : Ideal (normalizationBaseChange (A := A) (Ash := Ash)),
      p ∈ minimalPrimes (normalizationBaseChange (A := A) (Ash := Ash)) ∧ p ≤ m := sorry

end Unibranch.StrictHenselization
