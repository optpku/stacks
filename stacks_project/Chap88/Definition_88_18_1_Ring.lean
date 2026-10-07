module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.«88_3_0_1»

/-!
# Rig-smooth algebras and continuous homomorphisms

An algebra over a Noetherian pair `(A, I)` is rig-smooth when it is
topologically of finite type and some power of `I` annihilates
`Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. A continuous homomorphism of
adic Noetherian topological rings is rig-smooth when this holds for some,
equivalently any, ideal of definition of `A` that also induces the ambient
topology on `B`.
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Some power `I ^ c` annihilates `Ext¹_B(NL_{B/A}^∧, N)` for every
`B`-module `N`, computed from a finite completed presentation as the cokernel
of `Hom(⊕ᵢ B dx_i, N) → Hom(J / J², N)`. -/
def annihilatesExt1NaiveCotangent (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] (c : ℕ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
    ∀ (N : Type u) [AddCommGroup N] [Module B N],
      ∀ a ∈ I ^ c,
        ∀ f : P.toExtension.Cotangent →ₗ[B] N,
          ∃ k : (ι → B) →ₗ[B] N,
            ∀ x : P.toExtension.Cotangent,
              (algebraMap A B a) • f x = k (NaiveCotangent.Adic.jacobian P x)

/-- Annihilation of `Ext¹` of the completed naive cotangent complex unpacks as
the existence of a finite presentation whose Jacobian cokernels on Hom-spaces
are killed by every element of `I ^ c`. -/
theorem annihilatesExt1NaiveCotangent_iff (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] (c : ℕ) :
    annihilatesExt1NaiveCotangent I B c ↔
      ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
        ∀ (N : Type u) [AddCommGroup N] [Module B N],
          ∀ a ∈ I ^ c,
            ∀ f : P.toExtension.Cotangent →ₗ[B] N,
              ∃ k : (ι → B) →ₗ[B] N,
                ∀ x : P.toExtension.Cotangent,
                  (algebraMap A B a) • f x =
                    k (NaiveCotangent.Adic.jacobian P x) :=
  sorry

/-- An `A`-algebra `B` is rig-smooth over the pair `(A, I)` when it is
topologically of finite type and some power of `I` annihilates
`Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. -/
class RigSmooth (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop
    extends TopologicallyFiniteType I B where
  /-- Some power of `I` annihilates `Ext¹` of the completed naive cotangent
  complex. -/
  exists_pow_annihilates_ext1 : ∃ c : ℕ, annihilatesExt1NaiveCotangent I B c

namespace RigSmooth

/-- The identity algebra is rig-smooth over `(A, I)` whenever `A` is `I`-adically
complete. -/
instance id (I : Ideal A) [IsAdicComplete I A] : RigSmooth I A := sorry

/-- Rig-smoothness unpacks as topological finite type together with annihilation
of `Ext¹` of the completed naive cotangent complex by some power of `I`. -/
theorem iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    RigSmooth I B ↔
      TopologicallyFiniteType I B ∧
        ∃ c : ℕ, annihilatesExt1NaiveCotangent I B c :=
  sorry

/-- A rig-smooth algebra is topologically of finite type and has some power of
`I` annihilating `Ext¹` of the completed naive cotangent complex. -/
theorem spec (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [RigSmooth I B] :
    TopologicallyFiniteType I B ∧ ∃ c : ℕ, annihilatesExt1NaiveCotangent I B c :=
  sorry

end RigSmooth

end Algebra

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian topological rings is rig-smooth
when `B` is rig-smooth over `(A, I)` for some ideal of definition `I` of `A`
that induces the ambient topology on `B`. -/
class RigSmooth (φ : A →+* B) : Prop extends Continuous φ where
  /-- There is an ideal of definition of `A` inducing the topology on `B` and
  making `B` rig-smooth over `(A, I)` via `φ`. -/
  exists_idealOfDefinition :
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsAdic (Ideal.map φ I) ∧
          @Algebra.RigSmooth A _ I B _ φ.toAlgebra

namespace RigSmooth

/-- The identity of an adic Noetherian topological ring is rig-smooth. -/
instance id {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    RigSmooth (RingHom.id A) :=
  sorry

/-- Rig-smoothness of a continuous homomorphism is equivalent to the existence of
an ideal of definition of `A` inducing the topology on `B` and making the
target rig-smooth over the source. -/
theorem iff (φ : A →+* B) :
    RigSmooth φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigSmooth A _ I B _ φ.toAlgebra :=
  sorry

/-- Rig-smoothness may equivalently be tested on every ideal of definition. -/
theorem iff_forall_idealOfDefinition (φ : A →+* B) :
    RigSmooth φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          IsAdic (Ideal.map φ I) ∧
            @Algebra.RigSmooth A _ I B _ φ.toAlgebra :=
  sorry

/-- A rig-smooth homomorphism is an adic continuous map, topologically of finite
type, and annihilates `Ext¹` of the completed naive cotangent complex for some
ideal of definition of `A` inducing the topology on `B`. -/
theorem spec (φ : A →+* B) [RingHom.RigSmooth φ] :
    Continuous φ ∧ φ.IsAdicHom ∧
      ∃ I : Ideal A,
        TopologicalRing.Ideal.IsIdealOfDefinition I ∧
          IsAdic (Ideal.map φ I) ∧
            @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra ∧
              ∃ c : ℕ,
                @Algebra.annihilatesExt1NaiveCotangent A _ I B _ φ.toAlgebra c :=
  sorry

end RigSmooth

end RingHom
