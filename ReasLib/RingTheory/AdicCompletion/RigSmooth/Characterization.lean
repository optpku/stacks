module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Jacobian

/-!
# Characterization of rig-smooth algebras

Rig-smoothness of a topologically finite type algebra is equivalent to Ext-annihilation
of the completed naive cotangent complex, factorization through the Jacobian,
and existence of a finite Jacobian cover.
-/

@[expose] public section

universe u

open CategoryTheory
open Algebra.NaiveCotangent.Adic
open scoped PrimeSpectrum

/-- For an algebra topologically of finite type over a Noetherian pair `(A, I)`,
rig-smoothness is equivalent to annihilation of the derived Ext¹ of the completed
naive cotangent object by some power of `IB`, uniform scalar factorization through
the completed Jacobian by some power of `I`, and a finite cover by elementary
square Jacobian minors satisfying the relation condition modulo the square of
the presentation kernel. -/
@[stacks 0GAJ]
theorem Algebra.RigSmooth.tfae {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : NaiveCotangent.Adic.Presentation A B I ι) :
    List.TFAE
      ([RigSmooth I B,
        ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject I P)
          (I.map (algebraMap A B) ^ c),
        ∃ c : ℕ, ∀ a ∈ I ^ c, P.smulFactorsThroughJacobian a,
        P.HasJacobianCover]) :=
  sorry
