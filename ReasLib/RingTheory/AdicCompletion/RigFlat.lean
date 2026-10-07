module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.AdicCompletion.LocalizationAway
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Continuity
public import ReasLib.RingTheory.Topology.Adic.Hom

/-!
# Rig-flat homomorphisms of adic Noetherian rings

A continuous homomorphism of adic Noetherian topological rings is naively
rig-flat when it is adic, topologically of finite type, and localizations of
the target at topologically nilpotent elements of the source remain flat. It is
rig-flat when every induced map of completed principal localizations is naively
rig-flat.
-/

@[expose] public section

universe u

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalRing.IsAdicRing A]

/-- A homomorphism is topologically of finite type when some ideal of definition
of the source makes the target topologically of finite type as an algebra over
that pair. -/
def TopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ I : Ideal A,
    TopologicalRing.Ideal.IsIdealOfDefinition I ∧
      @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra

namespace TopologicallyFiniteType

/-- Exhibit topological finite type by an ideal of definition making the target
topologically of finite type over the source. -/
theorem of_algebra (φ : A →+* B) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (h : @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra) :
    φ.TopologicallyFiniteType :=
  sorry

/-- Topological finite type of a homomorphism unpacks as the existence of an
ideal of definition of the source making the target topologically of finite
type. -/
theorem iff (φ : A →+* B) :
    φ.TopologicallyFiniteType ↔
      ∃ I : Ideal A,
        TopologicalRing.Ideal.IsIdealOfDefinition I ∧
          @Algebra.TopologicallyFiniteType A _ I B _ φ.toAlgebra :=
  sorry

end TopologicallyFiniteType

end RingHom

namespace Algebra

variable {A : Type u} [CommRing A]

/-- An algebra over the pair `(A, I)` is naively rig-flat when it is
topologically of finite type and localizations of the target away from elements
with a power in `I` remain `A`-flat. -/
class NaiveRigFlat (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] : Prop
    extends TopologicallyFiniteType I B where
  /-- Localizing the target away from an element with a power in `I` preserves
  `A`-flatness. -/
  flat_of_pow_mem :
    ∀ a : A, (∃ n : ℕ, a ^ n ∈ I) → Module.Flat A (Localization.Away (algebraMap A B a))

namespace NaiveRigFlat

/-- The identity algebra is naively rig-flat over `(A, I)` whenever `A` is
`I`-adically complete. -/
instance id (I : Ideal A) [IsAdicComplete I A] : NaiveRigFlat I A := sorry

/-- Naive rig-flatness unpacks as topological finite type together with flatness
of localizations away from elements with a power in `I`. -/
theorem iff (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] :
    NaiveRigFlat I B ↔
      TopologicallyFiniteType I B ∧
        ∀ a : A, (∃ n : ℕ, a ^ n ∈ I) →
          Module.Flat A (Localization.Away (algebraMap A B a)) :=
  sorry

/-- A naively rig-flat algebra is topologically of finite type and remains flat
after localizing away from elements with a power in `I`. -/
theorem spec (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [NaiveRigFlat I B] :
    TopologicallyFiniteType I B ∧
      ∀ a : A, (∃ n : ℕ, a ^ n ∈ I) →
        Module.Flat A (Localization.Away (algebraMap A B a)) :=
  sorry

/-- Localizing a naively rig-flat algebra away from an element with a power in
`I` yields a flat module. -/
theorem flat_away (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [NaiveRigFlat I B] (a : A) (ha : ∃ n : ℕ, a ^ n ∈ I) :
    Module.Flat A (Localization.Away (algebraMap A B a)) :=
  sorry

end NaiveRigFlat

end Algebra

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian topological rings is naively
rig-flat when it is adic, topologically of finite type, and localizations of
the target at topologically nilpotent elements of the source remain flat. -/
class NaiveRigFlat (φ : A →+* B) : Prop extends Continuous φ where
  /-- The homomorphism is adic. -/
  isAdicHom : φ.IsAdicHom
  /-- The homomorphism is topologically of finite type. -/
  topologicallyFiniteType : φ.TopologicallyFiniteType
  /-- Localizing the target at the image of a topologically nilpotent element of
  the source preserves flatness. -/
  flat_of_topologicallyNilpotent :
    ∀ f : A, IsTopologicallyNilpotent f →
      ((algebraMap B (Localization.Away (φ f))).comp φ).Flat

namespace NaiveRigFlat

/-- The identity of an adic Noetherian topological ring is naively rig-flat. -/
instance id {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    NaiveRigFlat (RingHom.id A) :=
  sorry

/-- Naive rig-flatness unpacks as continuity, adicity, topological finite type,
and flatness of localizations at topologically nilpotent elements. -/
theorem iff (φ : A →+* B) :
    NaiveRigFlat φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧ φ.TopologicallyFiniteType ∧
        ∀ f : A, IsTopologicallyNilpotent f →
          ((algebraMap B (Localization.Away (φ f))).comp φ).Flat :=
  sorry

/-- A naively rig-flat homomorphism is adic, topologically of finite type, and
flat after localizing at topologically nilpotent elements. -/
theorem spec (φ : A →+* B) [NaiveRigFlat φ] :
    Continuous φ ∧ φ.IsAdicHom ∧ φ.TopologicallyFiniteType ∧
      ∀ f : A, IsTopologicallyNilpotent f →
        ((algebraMap B (Localization.Away (φ f))).comp φ).Flat :=
  sorry

end NaiveRigFlat

end RingHom

namespace completedPrincipalLocalization

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The induced map on principal localizations is adically continuous for the
extended ideals. -/
theorem awayMap_adicContinuous (φ : A →+* B) (I : Ideal A) (f : A) :
    (Localization.awayMap φ f).AdicContinuous
      (I.map (algebraMap A (Localization.Away f)))
      ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) :=
  RingHom.AdicContinuous.of_map_le <| by
    rw [Ideal.map_map, Ideal.map_map]
    have hcomp :
        (Localization.awayMap φ f).comp (algebraMap A (Localization.Away f)) =
          (algebraMap B (Localization.Away (φ f))).comp φ := by
      ext a
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [hcomp]

/-- The canonical map of completed principal localizations induced by a ring
homomorphism. -/
noncomputable def map (φ : A →+* B) (I : Ideal A) (f : A) :
    completedPrincipalLocalization I f →+*
      completedPrincipalLocalization (I.map φ) (φ f) :=
  RingHom.AdicContinuous.completionMap (awayMap_adicContinuous φ I f)

/-- `map` is the completion map of `awayMap_adicContinuous`. -/
theorem map_eq (φ : A →+* B) (I : Ideal A) (f : A) :
    map φ I f =
      RingHom.AdicContinuous.completionMap (awayMap_adicContinuous φ I f) :=
  sorry

/-- `map` extends `Localization.awayMap` through the canonical maps from
principal localizations. -/
theorem map_comp_away (φ : A →+* B) (I : Ideal A) (f : A) :
    (map φ I f).comp (ofAway I f) =
      (ofAway (I.map φ) (φ f)).comp (Localization.awayMap φ f) :=
  sorry

/-- `map` extends `φ` through the canonical maps from `A` and `B`. -/
theorem map_comp (φ : A →+* B) (I : Ideal A) (f : A) :
    (map φ I f).comp (of I f) = (of (I.map φ) (φ f)).comp φ :=
  sorry

end completedPrincipalLocalization

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian topological rings is rig-flat
when it is adic, topologically of finite type, and every induced map of
completed principal localizations is naively rig-flat. -/
class RigFlat (φ : A →+* B) : Prop extends Continuous φ where
  /-- The homomorphism is adic. -/
  isAdicHom : φ.IsAdicHom
  /-- The homomorphism is topologically of finite type. -/
  topologicallyFiniteType : φ.TopologicallyFiniteType
  /-- Every completed principal localization of `φ` is naively rig-flat over the
  extended ideal of definition. -/
  naive_completed :
    ∀ (f : A) (I : Ideal A), TopologicalRing.Ideal.IsIdealOfDefinition I →
      @Algebra.NaiveRigFlat (completedPrincipalLocalization I f) _
        (I.map (completedPrincipalLocalization.of I f))
        (completedPrincipalLocalization (I.map φ) (φ f)) _
        (completedPrincipalLocalization.map φ I f).toAlgebra

namespace RigFlat

/-- The identity of an adic Noetherian topological ring is rig-flat. -/
instance id {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    RigFlat (RingHom.id A) :=
  sorry

/-- Rig-flatness unpacks as continuity, adicity, topological finite type, and
naive rig-flatness of every completed principal localization. -/
theorem iff (φ : A →+* B) :
    RigFlat φ ↔
      Continuous φ ∧ φ.IsAdicHom ∧ φ.TopologicallyFiniteType ∧
        ∀ (f : A) (I : Ideal A), TopologicalRing.Ideal.IsIdealOfDefinition I →
          @Algebra.NaiveRigFlat (completedPrincipalLocalization I f) _
            (I.map (completedPrincipalLocalization.of I f))
            (completedPrincipalLocalization (I.map φ) (φ f)) _
            (completedPrincipalLocalization.map φ I f).toAlgebra :=
  sorry

/-- A rig-flat homomorphism is adic, topologically of finite type, and induces
naively rig-flat maps on completed principal localizations. -/
theorem spec (φ : A →+* B) [RigFlat φ] :
    Continuous φ ∧ φ.IsAdicHom ∧ φ.TopologicallyFiniteType ∧
      ∀ (f : A) (I : Ideal A), TopologicalRing.Ideal.IsIdealOfDefinition I →
        @Algebra.NaiveRigFlat (completedPrincipalLocalization I f) _
          (I.map (completedPrincipalLocalization.of I f))
          (completedPrincipalLocalization (I.map φ) (φ f)) _
          (completedPrincipalLocalization.map φ I f).toAlgebra :=
  sorry

/-- Setting `f = 1` in the definition, every rig-flat homomorphism is naively
rig-flat. -/
theorem toNaive (φ : A →+* B) [RigFlat φ] : NaiveRigFlat φ := sorry

/-- Rig-flatness descends across a commutative square with `A →+* A'` flat and
`B →+* B'` faithfully flat. -/
theorem of_faithfullyFlat_square
    {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing A'] [TopologicalRing.IsAdicRing B']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing A'] [IsNoetherianRing B']
    (φ : A →+* B) (φ' : A' →+* B') (fA : A →+* A') (fB : B →+* B')
    (h_comm : φ'.comp fA = fB.comp φ)
    (hφ_adic : φ.IsAdicHom) (hφ'_adic : φ'.IsAdicHom)
    (hfA_adic : fA.IsAdicHom) (hfB_adic : fB.IsAdicHom)
    (hφ_tft : φ.TopologicallyFiniteType) (hφ'_tft : φ'.TopologicallyFiniteType)
    (hfA_tft : fA.TopologicallyFiniteType) (hfB_tft : fB.TopologicallyFiniteType)
    (hfA_flat : fA.Flat) (hfB_fflat : fB.FaithfullyFlat) (hφ' : RigFlat φ') :
    RigFlat φ :=
  sorry

end RigFlat

end RingHom
