/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

/-!
# Rig-étale algebras and continuous homomorphisms

An algebra over a Noetherian pair `(A, I)` is rig-étale when it is
topologically of finite type and some power of `I` annihilates the homology of
the completed naive cotangent complex `NL_{B/A}^∧` in degrees `1` and `0`. A
continuous homomorphism of adic Noetherian topological rings is rig-étale when
this holds for some, equivalently any, ideal of definition of `A` that also
induces the ambient topology on `B`.
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Every `a ∈ I ^ c` annihilates homology of a finite completed naive
cotangent complex of `B` over `(A, I)` in degrees `1` and `0`. -/
def annihilatesNaiveCotangent (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    (c : ℕ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
    ∀ a ∈ I ^ c,
      (∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 1 : Type u),
          (algebraMap A B a) • x = 0) ∧
        ∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 0 : Type u),
          (algebraMap A B a) • x = 0

/-- Annihilation of completed naive cotangent homology unpacks as the existence
of a finite presentation whose homology in degrees `1` and `0` is killed by
every element of `I ^ c`. -/
theorem annihilatesNaiveCotangent_iff (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] (c : ℕ) :
    annihilatesNaiveCotangent I B c ↔
      ∃ (ι : Type u) (_ : Fintype ι) (P : NaiveCotangent.Adic.Presentation A B I ι),
        ∀ a ∈ I ^ c,
          (∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 1 : Type u),
              (algebraMap A B a) • x = 0) ∧
            ∀ x : ((NaiveCotangent.Adic.naiveCotangent I P).homology 0 : Type u),
              (algebraMap A B a) • x = 0 :=
  sorry

/-- An `A`-algebra `B` is rig-étale over the pair `(A, I)` when it is
topologically of finite type and some power of `I` annihilates completed naive
cotangent homology. -/
class RigEtale (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop
    extends TopologicallyFiniteType I B where
  /-- Some power of `I` annihilates completed naive cotangent homology. -/
  exists_pow_annihilates : ∃ c : ℕ, annihilatesNaiveCotangent I B c

namespace RigEtale

/-- The identity algebra is rig-étale over `(A, I)` whenever `A` is `I`-adically
complete. -/
instance id (I : Ideal A) [IsAdicComplete I A] : RigEtale I A := sorry

/-- Rig-étaleness unpacks as topological finite type together with annihilation
of completed naive cotangent homology by some power of `I`. -/
theorem iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    RigEtale I B ↔
      TopologicallyFiniteType I B ∧ ∃ c : ℕ, annihilatesNaiveCotangent I B c :=
  sorry

/-- A rig-étale algebra is topologically of finite type and has some power of
`I` annihilating completed naive cotangent homology. -/
theorem spec (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [RigEtale I B] :
    TopologicallyFiniteType I B ∧ ∃ c : ℕ, annihilatesNaiveCotangent I B c :=
  sorry

end RigEtale

end Algebra

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian topological rings is rig-étale
when `B` is rig-étale over `(A, I)` for some ideal of definition `I` of `A`
that induces the ambient topology on `B`. -/
class RigEtale (φ : A →+* B) : Prop extends Continuous φ where
  /-- There is an ideal of definition of `A` inducing the topology on `B` and
  making `B` rig-étale over `(A, I)` via `φ`. -/
  exists_idealOfDefinition :
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsAdic (Ideal.map φ I) ∧
          @Algebra.RigEtale A _ I B _ φ.toAlgebra

namespace RigEtale

/-- The identity of an adic Noetherian topological ring is rig-étale. -/
instance id {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    RigEtale (RingHom.id A) :=
  sorry

/-- Rig-étaleness of a continuous homomorphism is equivalent to the existence of
an ideal of definition of `A` inducing the topology on `B` and making the
target rig-étale over the source. -/
theorem iff (φ : A →+* B) :
    RigEtale φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigEtale A _ I B _ φ.toAlgebra :=
  sorry

/-- Rig-étaleness may equivalently be tested on every ideal of definition. -/
theorem iff_forall_idealOfDefinition (φ : A →+* B) :
    RigEtale φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          IsAdic (Ideal.map φ I) ∧
            @Algebra.RigEtale A _ I B _ φ.toAlgebra :=
  sorry

/-- A rig-étale homomorphism is an adic continuous map, topologically of finite
type, and annihilates completed naive cotangent homology for some ideal of
definition of `A` inducing the topology on `B`. -/
theorem spec (φ : A →+* B) [RingHom.RigEtale φ] :
    Continuous φ ∧ φ.IsAdicHom ∧
      ∃ I : Ideal A,
        TopologicalRing.Ideal.IsIdealOfDefinition I ∧
          IsAdic (Ideal.map φ I) ∧
            @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra ∧
              ∃ c : ℕ, @Algebra.annihilatesNaiveCotangent A _ I B _ φ.toAlgebra c :=
  sorry

end RigEtale

end RingHom
