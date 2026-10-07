module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap87.Definition_87_9_9_Spf
public import stacks_project.Chap87.«87_21_2_1_Completion»

/-!
# Weak-ideal completion maps

An algebra map `A →ₐ[B] A'` induces a continuous map of weak-ideal completions
`(A)^∧ → (A')^∧`. The composite `Spec((A)^∧) ⟶ Spec(B) ⟶ S` is the structure
morphism needed to form `Spf((A)^∧)` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing

noncomputable section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {B A A' : Type u} [CommRing B] [TopologicalSpace B]
  [CommRing A] [Algebra B A] [CommRing A'] [Algebra B A']

/-- Stage ideals `I A` map into `I A'` under a `B`-algebra homomorphism. -/
theorem map_le_comap (f : A →ₐ[B] A') (I : Ideal B) :
    I.map (algebraMap B A) ≤ (I.map (algebraMap B A')).comap f :=
  sorry

/-- The ring map `(A)^∧ →+* (A')^∧` induced by a `B`-algebra map, acting stagewise
by the quotient maps `A ⧸ I A →+* A' ⧸ I A'`. -/
def map (f : A →ₐ[B] A') :
    weakIdealCompletion B A →+* weakIdealCompletion B A' where
  toFun x :=
    ⟨fun I =>
        Ideal.quotientMap (I.1.map (algebraMap B A')) (f : A →+* A')
          (map_le_comap f I.1) (x.val I),
      fun {I J} hJI => sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- `map` sends the identity algebra map to the identity on the completion. -/
theorem map_id : map (AlgHom.id B A) = RingHom.id (weakIdealCompletion B A) :=
  sorry

/-- `map` is compatible with composition of algebra maps. -/
theorem map_comp {A'' : Type u} [CommRing A''] [Algebra B A'']
    (f : A →ₐ[B] A') (g : A' →ₐ[B] A'') :
    map (g.comp f) = (map g).comp (map f) :=
  sorry

/-- Stage evaluation intertwines `map` with the induced quotient homomorphism. -/
theorem eval_map (f : A →ₐ[B] A') {I : Ideal B}
    (hI : Ideal.IsWeakIdealOfDefinition I) (x : weakIdealCompletion B A) :
    eval B A' hI (map f x) =
      Ideal.quotientMap (I.map (algebraMap B A')) (f : A →+* A')
        (map_le_comap f I) (eval B A hI x) :=
  sorry

/-- The induced map of weak-ideal completions is continuous. -/
theorem continuous_map (f : A →ₐ[B] A') : Continuous (map f) :=
  sorry

end TopologicalRing.weakIdealCompletion

namespace TopologicalRing

variable (B A : Type u) [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]

/-- The algebra map `B → (A)^∧` is continuous. -/
theorem continuous_algebraMap :
    Continuous (algebraMap B (weakIdealCompletion B A)) :=
  sorry

/-- The weak-ideal completion of a `B`-algebra is weakly admissible when `B` is. -/
instance instIsWeaklyAdmissibleRing_weakIdealCompletion
    [IsWeaklyAdmissibleRing B] :
    IsWeaklyAdmissibleRing (weakIdealCompletion B A) :=
  sorry

end TopologicalRing

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

open TopologicalRing

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]

/-- The structure morphism `Spec((A)^∧) ⟶ S` of the weak-ideal completion of a
`B`-algebra, obtained by composing `Spec` of `B → (A)^∧` with the structure
morphism of `B`. -/
def specHom_weakIdealCompletion (hB : Spec (.of B) ⟶ S) (A : Type u)
    [CommRing A] [Algebra B A] :
    Spec (.of (weakIdealCompletion B A)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap B (weakIdealCompletion B A))) ≫ hB

/-- `specHom_weakIdealCompletion` is `Spec` of the algebra map `B → (A)^∧`
followed by the structure morphism of `B`. -/
theorem specHom_weakIdealCompletion_comp (hB : Spec (.of B) ⟶ S) (A : Type u)
    [CommRing A] [Algebra B A] :
    specHom_weakIdealCompletion hB A =
      Spec.map (CommRingCat.ofHom (algebraMap B (weakIdealCompletion B A))) ≫ hB :=
  sorry

/-- Continuous `B`-algebra maps of weak-ideal completions of étale `B`-algebras
are uniquely of the form `weakIdealCompletion.map f`. -/
theorem existsUnique_eq_weakIdealCompletion_map {A A' : Type u} [CommRing A]
    [Algebra B A] [Algebra.Etale B A] [CommRing A'] [Algebra B A']
    [Algebra.Etale B A'] (φ : weakIdealCompletion B A →+* weakIdealCompletion B A')
    (hφ : Continuous φ)
    (hw : φ.comp (algebraMap B (weakIdealCompletion B A)) =
      algebraMap B (weakIdealCompletion B A')) :
    ∃! f : A →ₐ[B] A', φ = weakIdealCompletion.map f :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
