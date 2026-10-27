/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Weak-ideal completion maps

An algebra map `A →ₐ[B] A'` induces a continuous map of weak-ideal completions
`(A)^∧ → (A')^∧`. The structural map from the base is continuous when the base topology is compatible
with its ring operations.
-/

@[expose] public section

open TopologicalRing

noncomputable section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {B A A' : Type u} [CommRing B] [TopologicalSpace B]
  [CommRing A] [Algebra B A] [CommRing A'] [Algebra B A']

/-- Stage ideals `I A` map into `I A'` under a `B`-algebra homomorphism. -/
theorem map_le_comap (f : A →ₐ[B] A') (I : Ideal B) :
    I.map (algebraMap B A) ≤ (I.map (algebraMap B A')).comap f := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  change f (algebraMap B A b) ∈ I.map (algebraMap B A')
  rw [f.commutes]
  exact Ideal.mem_map_of_mem _ hb

/-- Stagewise quotient maps preserve compatibility of inverse-limit families. -/
theorem map_compat (f : A →ₐ[B] A') (x : weakIdealCompletion B A)
    {I J : {I : Ideal B // Ideal.IsWeakIdealOfDefinition I}} (hJI : J.1 ≤ I.1) :
    weakIdealTransition B A' hJI
        (Ideal.quotientMap (J.1.map (algebraMap B A')) (f : A →+* A')
          (map_le_comap f J.1) (x.val J)) =
      Ideal.quotientMap (I.1.map (algebraMap B A')) (f : A →+* A')
        (map_le_comap f I.1) (x.val I) := by
  have h : ∀ z : A ⧸ J.1.map (algebraMap B A),
      weakIdealTransition B A' hJI
          (Ideal.quotientMap (J.1.map (algebraMap B A')) (f : A →+* A')
            (map_le_comap f J.1) z) =
        Ideal.quotientMap (I.1.map (algebraMap B A')) (f : A →+* A')
          (map_le_comap f I.1) (weakIdealTransition B A hJI z) := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  rw [h, x.property (I := I) (J := J) hJI]

/-- The ring homomorphism of completions induced stagewise by an algebra homomorphism. -/
def map (f : A →ₐ[B] A') :
    weakIdealCompletion B A →+* weakIdealCompletion B A' where
  toFun x :=
    ⟨fun I =>
        Ideal.quotientMap (I.1.map (algebraMap B A')) (f : A →+* A')
          (map_le_comap f I.1) (x.val I),
      fun hJI => map_compat f x hJI⟩
  map_one' := by
    apply Subtype.ext
    funext I
    exact map_one (Ideal.quotientMap _ (f : A →+* A') (map_le_comap f I.1))
  map_mul' x y := by
    apply Subtype.ext
    funext I
    exact map_mul (Ideal.quotientMap _ (f : A →+* A') (map_le_comap f I.1)) _ _
  map_zero' := by
    apply Subtype.ext
    funext I
    exact map_zero (Ideal.quotientMap _ (f : A →+* A') (map_le_comap f I.1))
  map_add' x y := by
    apply Subtype.ext
    funext I
    exact map_add (Ideal.quotientMap _ (f : A →+* A') (map_le_comap f I.1)) _ _

/-- `map` sends the identity algebra map to the identity on the completion. -/
theorem map_id : map (AlgHom.id B A) = RingHom.id (weakIdealCompletion B A) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  funext I
  change Ideal.quotientMap _ (AlgHom.id B A : A →+* A) _ (x.val I) = x.val I
  generalize x.val I = z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- `map` is compatible with composition of algebra maps. -/
theorem map_comp {A'' : Type u} [CommRing A''] [Algebra B A'']
    (f : A →ₐ[B] A') (g : A' →ₐ[B] A'') :
    map (g.comp f) = (map g).comp (map f) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  funext I
  change Ideal.quotientMap _ (g.comp f : A →+* A'') _ (x.val I) =
    Ideal.quotientMap _ (g : A' →+* A'') _
      (Ideal.quotientMap _ (f : A →+* A') _ (x.val I))
  generalize x.val I = z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- Stage evaluation intertwines `map` with the induced quotient homomorphism. -/
theorem eval_map (f : A →ₐ[B] A') {I : Ideal B}
    (hI : Ideal.IsWeakIdealOfDefinition I) (x : weakIdealCompletion B A) :
    eval B A' hI (map f x) =
      Ideal.quotientMap (I.map (algebraMap B A')) (f : A →+* A')
        (map_le_comap f I) (eval B A hI x) :=
  rfl

/-- The induced map of weak-ideal completions is continuous. -/
theorem continuous_map (f : A →ₐ[B] A') : Continuous (map f) := by
  letI : ∀ I : {I : Ideal B // Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace (A ⧸ I.1.map (algebraMap B A)) := fun _ => ⊥
  letI : ∀ I : {I : Ideal B // Ideal.IsWeakIdealOfDefinition I},
      DiscreteTopology (A ⧸ I.1.map (algebraMap B A)) := fun _ => ⟨rfl⟩
  letI : ∀ I : {I : Ideal B // Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace (A' ⧸ I.1.map (algebraMap B A')) := fun _ => ⊥
  apply (weakIdealCompletion.continuous_iff B A' _).2
  intro I
  have h : @Continuous (A ⧸ I.1.map (algebraMap B A))
      (A' ⧸ I.1.map (algebraMap B A')) (inferInstance : TopologicalSpace _) ⊥
      (Ideal.quotientMap _ (f : A →+* A') (map_le_comap f I.1)) :=
    continuous_of_discreteTopology
  exact h.comp (continuous_eval B A I.property)

end TopologicalRing.weakIdealCompletion

namespace TopologicalRing

variable (B A : Type u) [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]

/-- The algebra map `B → (A)^∧` is continuous. -/
theorem continuous_algebraMap [IsTopologicalRing B] :
    Continuous (algebraMap B (weakIdealCompletion B A)) := by
  apply (weakIdealCompletion.continuous_iff B A _).2
  intro I
  letI : TopologicalSpace (A ⧸ I.1.map (algebraMap B A)) := ⊥
  letI : DiscreteTopology (A ⧸ I.1.map (algebraMap B A)) := ⟨rfl⟩
  let f : B →+* A ⧸ I.1.map (algebraMap B A) :=
    (Ideal.Quotient.mk _).comp (algebraMap B A)
  change Continuous f
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero,
    nhds_discrete (A ⧸ I.1.map (algebraMap B A)), Filter.tendsto_pure]
  exact Filter.mem_of_superset (I.property.1.mem_nhds I.1.zero_mem)
    (fun b hb => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hb))

/-- The weak-ideal completion of a `B`-algebra is weakly admissible when `B` is. -/
instance instIsWeaklyAdmissibleRing_weakIdealCompletion
    [IsWeaklyAdmissibleRing B] :
    IsWeaklyAdmissibleRing (weakIdealCompletion B A) :=
  weakIdealCompletion.isWeaklyAdmissibleRing B A

end TopologicalRing

