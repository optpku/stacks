/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Weak-ideal completion of an algebra

Given a topological ring `A` and an `A`-algebra `A'` without a topology, the weak-ideal
completion of `A'` is the inverse limit of `A' ⧸ I A'` over the weak ideals of definition
of `A`.
-/

@[expose] public section

open Filter Topology
open scoped Topology

noncomputable section

universe u

namespace TopologicalRing

variable (A A' : Type u) [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A']

/-- The transition map `A' ⧸ J A' →+* A' ⧸ I A'` of the inverse system, for `J ≤ I`. -/
def weakIdealTransition {I J : Ideal A} (hJI : J ≤ I) :
    A' ⧸ J.map (algebraMap A A') →+* A' ⧸ I.map (algebraMap A A') :=
  Ideal.Quotient.factor (Ideal.map_mono hJI)

/-- The completion `(A')^∧` of an `A`-algebra along the weak ideals of definition of `A`,
realized as compatible families in `Π I, A' ⧸ I A'`. -/
def weakIdealCompletion : Type u :=
  { f : ∀ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      A' ⧸ I.1.map (algebraMap A A') //
    ∀ {I J : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I}} (hJI : J.1 ≤ I.1),
      weakIdealTransition A A' hJI (f J) = f I }

namespace weakIdealCompletion

/-- Zero is the zero family of residue classes. -/
instance instZero : Zero (weakIdealCompletion A A') where
  zero := ⟨0, fun _ => map_zero _⟩

/-- Pointwise addition of compatible families. -/
instance instAdd : Add (weakIdealCompletion A A') where
  add x y := ⟨x.val + y.val, by
    intro I J h
    change weakIdealTransition A A' h (x.val J + y.val J) = x.val I + y.val I
    rw [map_add, x.property h, y.property h]⟩

/-- Pointwise negation of compatible families. -/
instance instNeg : Neg (weakIdealCompletion A A') where
  neg x := ⟨-x.val, by
    intro I J h
    change weakIdealTransition A A' h (-x.val J) = -x.val I
    rw [map_neg, x.property h]⟩

/-- Pointwise subtraction of compatible families. -/
instance instSub : Sub (weakIdealCompletion A A') where
  sub x y := ⟨x.val - y.val, by
    intro I J h
    change weakIdealTransition A A' h (x.val J - y.val J) = x.val I - y.val I
    rw [map_sub, x.property h, y.property h]⟩

/-- Natural-number scalar multiplication on compatible families. -/
instance instNSmul : SMul ℕ (weakIdealCompletion A A') where
  smul n x := ⟨n • x.val, by
    intro I J h
    change weakIdealTransition A A' h (n • x.val J) = n • x.val I
    rw [map_nsmul, x.property h]⟩

/-- Integer scalar multiplication on compatible families. -/
instance instZSmul : SMul ℤ (weakIdealCompletion A A') where
  smul n x := ⟨n • x.val, by
    intro I J h
    change weakIdealTransition A A' h (n • x.val J) = n • x.val I
    rw [map_zsmul, x.property h]⟩

/-- One is the unit family of residue classes. -/
instance instOne : One (weakIdealCompletion A A') where
  one := ⟨1, fun _ => map_one _⟩

/-- Pointwise multiplication of compatible families. -/
instance instMul : Mul (weakIdealCompletion A A') where
  mul x y := ⟨x.val * y.val, by
    intro I J h
    change weakIdealTransition A A' h (x.val J * y.val J) = x.val I * y.val I
    rw [map_mul, x.property h, y.property h]⟩

/-- Pointwise natural-number powers of compatible families. -/
instance instPow : Pow (weakIdealCompletion A A') ℕ where
  pow x n := ⟨x.val ^ n, by
    intro I J h
    change weakIdealTransition A A' h (x.val J ^ n) = x.val I ^ n
    rw [map_pow, x.property h]⟩

/-- Natural-number cast of compatible families. -/
instance instNatCast : NatCast (weakIdealCompletion A A') where
  natCast n := ⟨n, fun _ => map_natCast _ _⟩

/-- Integer cast of compatible families. -/
instance instIntCast : IntCast (weakIdealCompletion A A') where
  intCast n := ⟨n, fun _ => map_intCast _ _⟩

/-- The weak-ideal completion is a commutative ring under pointwise operations. -/
instance instCommRing : CommRing (weakIdealCompletion A A') :=
  Subtype.val_injective.commRing (fun x : weakIdealCompletion A A' => x.val)
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The inverse-limit topology, induced from the product of discrete topologies on the
stage quotients `A' ⧸ I A'`. -/
instance instTopologicalSpace : TopologicalSpace (weakIdealCompletion A A') :=
  TopologicalSpace.induced Subtype.val <|
    ⨅ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace.induced (fun f => f I)
        (⊥ : TopologicalSpace (A' ⧸ I.1.map (algebraMap A A')))

/-- Canonical map from `A'` into the inverse-limit completion. -/
def of : A' →+* weakIdealCompletion A A' where
  toFun x := ⟨fun _ => Ideal.Quotient.mk _ x, fun _ => rfl⟩
  map_one' := by
    apply Subtype.ext
    funext I
    exact map_one (Ideal.Quotient.mk (I.1.map (algebraMap A A')))
  map_mul' x y := by
    apply Subtype.ext
    funext I
    exact map_mul (Ideal.Quotient.mk (I.1.map (algebraMap A A'))) x y
  map_zero' := by
    apply Subtype.ext
    funext I
    exact map_zero (Ideal.Quotient.mk (I.1.map (algebraMap A A')))
  map_add' x y := by
    apply Subtype.ext
    funext I
    exact map_add (Ideal.Quotient.mk (I.1.map (algebraMap A A'))) x y

/-- Projection from the completion onto the stage quotient `A' ⧸ I A'`. -/
def eval {I : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I) :
    weakIdealCompletion A A' →+* A' ⧸ I.map (algebraMap A A') where
  toFun x := x.val ⟨I, hI⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Families in the completion are compatible with the inverse-system transitions. -/
theorem val_compat (x : weakIdealCompletion A A')
    {I J : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I)
    (hJ : Ideal.IsWeakIdealOfDefinition J) (hJI : J ≤ I) :
    weakIdealTransition A A' hJI (eval A A' hJ x) = eval A A' hI x :=
  x.property (I := ⟨I, hI⟩) (J := ⟨J, hJ⟩) hJI

/-- Equality of completions is equality of all stage projections. -/
theorem ext {x y : weakIdealCompletion A A'}
    (h : ∀ (I : Ideal A) (hI : Ideal.IsWeakIdealOfDefinition I),
      eval A A' hI x = eval A A' hI y) : x = y := by
  apply Subtype.ext
  funext I
  exact h I.val I.property

/-- Stage projection of the canonical map `A' → (A')^∧` is the quotient map. -/
theorem eval_of {I : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I) (x : A') :
    eval A A' hI (of A A' x) = Ideal.Quotient.mk _ x := rfl

/-- The completion is an `A'`-algebra via `weakIdealCompletion.of`. -/
instance instAlgebra : Algebra A' (weakIdealCompletion A A') := (of A A').toAlgebra

/-- The completion is an `A`-algebra via `A → A' → (A')^∧`, the horizontal arrow of the
localization square. -/
instance instAlgebraBase : Algebra A (weakIdealCompletion A A') :=
  ((of A A').comp (algebraMap A A')).toAlgebra

/-- The `A`-algebra structure on the completion factors through `A'`. -/
instance instIsScalarTower : IsScalarTower A A' (weakIdealCompletion A A') :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The algebra map `A → (A')^∧` is the composition of `algebraMap A A'` with
`weakIdealCompletion.of`. -/
theorem algebraMap_eq :
    algebraMap A (weakIdealCompletion A A') = (of A A').comp (algebraMap A A') := rfl

/-- Addition and multiplication are continuous on the inverse-limit topology. -/
instance instIsTopologicalRing : IsTopologicalRing (weakIdealCompletion A A') := by
  letI : ∀ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⊥
  letI : ∀ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      @DiscreteTopology (A' ⧸ I.1.map (algebraMap A A')) (inferInstance : TopologicalSpace _) :=
    fun _ => ⟨rfl⟩
  let e : weakIdealCompletion A A' →+*
      ∀ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
        A' ⧸ I.1.map (algebraMap A A') :=
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact
    { toContinuousAdd := ContinuousAdd.induced e
      toContinuousMul := ContinuousMul.induced e
      toContinuousNeg := ContinuousNeg.induced e }

/-- Continuity into the completion is continuity of every discrete stage projection. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → weakIdealCompletion A A') :
    Continuous f ↔ ∀ I : {I : Ideal A // Ideal.IsWeakIdealOfDefinition I},
      @Continuous X (A' ⧸ I.1.map (algebraMap A A')) _ ⊥ (fun x => (f x).val I) := by
  change @Continuous X (weakIdealCompletion A A') _
    (TopologicalSpace.induced Subtype.val _) f ↔ _
  simp only [continuous_induced_rng, continuous_iInf_rng, Function.comp_def]

/-- Projection to a discrete quotient stage is continuous. -/
theorem continuous_eval {I : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I) :
    @Continuous (weakIdealCompletion A A') (A' ⧸ I.map (algebraMap A A')) _ ⊥
      (eval A A' hI) :=
  (continuous_iff A A' id).1 continuous_id ⟨I, hI⟩


/-- The inverse-limit topology has a basis of ideals given by finite intersections
of the kernels of its discrete stage projections. -/
instance instIsLinearTopology :
    IsLinearTopology (weakIdealCompletion A A') (weakIdealCompletion A A') := by
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⊥
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      DiscreteTopology (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⟨rfl⟩
  have hn : 𝓝 (0 : weakIdealCompletion A A') =
      ⨅ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
        Filter.principal {x : weakIdealCompletion A A' | x.val I = 0} := by
    change @nhds (weakIdealCompletion A A') (TopologicalSpace.induced Subtype.val _) 0 = _
    rw [nhds_induced, nhds_pi, Filter.pi]
    simp only [Filter.comap_iInf, nhds_discrete, Filter.comap_pure, Filter.comap_principal]
    rfl
  have hb := Filter.hasBasis_iInf_principal_finite
    (fun I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I} =>
      {x : weakIdealCompletion A A' | x.val I = 0})
  rw [← hn] at hb
  refine IsLinearTopology.mk_of_hasBasis (weakIdealCompletion A A')
    (p := fun t : Set {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I} => t.Finite)
    (s := fun t : Set {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I} =>
      ⨅ I ∈ t, RingHom.ker (weakIdealCompletion.eval A A' I.property)) ?_
  convert hb using 1
  ext x
  simp [RingHom.mem_ker, weakIdealCompletion.eval]

/-- Distinct compatible families are separated by a discrete stage projection. -/
instance instT2Space : T2Space (weakIdealCompletion A A') := by
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⊥
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      DiscreteTopology (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⟨rfl⟩
  exact (show IsEmbedding (fun x : weakIdealCompletion A A' => x.val) from
    ⟨⟨rfl⟩, Subtype.val_injective⟩).t2Space

/-- Compatible families form a closed subgroup of the product of complete discrete
quotients, hence are complete for the canonical additive uniformity. -/
theorem completeSpace : @CompleteSpace (weakIdealCompletion A A')
    (IsTopologicalAddGroup.rightUniformSpace (weakIdealCompletion A A')) := by
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      UniformSpace (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⊥
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      DiscreteUniformity (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⟨rfl⟩
  letI : UniformSpace (weakIdealCompletion A A') :=
    IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (weakIdealCompletion A A') :=
    isUniformAddGroup_of_addCommGroup
  let e := RingHom.pi (fun I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I} =>
    weakIdealCompletion.eval A A' I.property)
  have he : IsInducing e := ⟨rfl⟩
  have hu : IsUniformInducing e :=
    AddMonoidHom.isUniformInducing_of_isInducing (f := e.toAddMonoidHom) he
  apply hu.completeSpace
  apply IsClosed.isComplete
  have hr : Set.range e = {v | ∀ (I J : {I : Ideal A //
      TopologicalRing.Ideal.IsWeakIdealOfDefinition I}) (h : J.1 ≤ I.1),
      weakIdealTransition A A' h (v J) = v I} := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩ I J h
      exact x.property (I := I) (J := J) h
    · intro h
      exact ⟨⟨v, fun {I J} hJI => h I J hJI⟩, rfl⟩
  rw [hr]
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun I => isClosed_iInter fun J => isClosed_iInter fun h => ?_
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply J)) (continuous_apply I)

/-- A stage kernel is an open ideal of topologically nilpotent elements. This only
uses the weak-ideal property of the chosen base stage. -/
theorem eval_ker_isWeakIdealOfDefinition {J : Ideal A}
    (hJ : TopologicalRing.Ideal.IsWeakIdealOfDefinition J) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (RingHom.ker (eval A A' hJ)) := by
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      TopologicalSpace (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⊥
  letI : ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
      DiscreteTopology (A' ⧸ I.1.map (algebraMap A A')) := fun _ => ⟨rfl⟩
  letI : TopologicalSpace (A' ⧸ J.map (algebraMap A A')) := ⊥
  letI : DiscreteTopology (A' ⧸ J.map (algebraMap A A')) := ⟨rfl⟩
  constructor
  · change IsOpen ((weakIdealCompletion.eval A A' hJ) ⁻¹' {0})
    exact (isOpen_discrete _).preimage (weakIdealCompletion.continuous_eval A A' hJ)
  · intro x hx
    change Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)
    apply tendsto_subtype_rng.2
    apply tendsto_pi_nhds.2
    intro I
    change _root_.IsTopologicallyNilpotent (x.val I)
    apply IsNilpotent.isTopologicallyNilpotent
    let K : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I} :=
      ⟨I.1 ⊓ J, ⟨I.property.1.inter hJ.1, fun b hb => I.property.2 b hb.1⟩⟩
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val K)
    have haJ : a ∈ J.map (algebraMap A A') := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      calc
        Ideal.Quotient.mk _ a =
            weakIdealTransition A A' (show K.1 ≤ J from inf_le_right)
              (Ideal.Quotient.mk _ a) := rfl
        _ = weakIdealTransition A A' (show K.1 ≤ J from inf_le_right) (x.val K) :=
          congrArg _ ha
        _ = x.val ⟨J, hJ⟩ := x.property (I := ⟨J, hJ⟩) (J := K) inf_le_right
        _ = 0 := hx
    have haI : Ideal.Quotient.mk (I.1.map (algebraMap A A')) a = x.val I := by
      calc
        _ = weakIdealTransition A A' (show K.1 ≤ I.1 from inf_le_left)
              (Ideal.Quotient.mk _ a) := rfl
        _ = weakIdealTransition A A' (show K.1 ≤ I.1 from inf_le_left) (x.val K) :=
          congrArg _ ha
        _ = x.val I := x.property (I := I) (J := K) inf_le_left
    have hJI : J ≤ I.1.radical := by
      intro b hb
      exact (_root_.IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds (hJ.2 b hb)
        (I.property.1.mem_nhds I.1.zero_mem))
    have hm : J.map (algebraMap A A') ≤ (I.1.map (algebraMap A A')).radical :=
      (Ideal.map_mono hJI).trans (Ideal.map_radical_le (algebraMap A A'))
    obtain ⟨n, hn⟩ := hm haJ
    refine ⟨n, ?_⟩
    rw [← haI, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- A weakly pre-admissible base supplies a genuine weak ideal of definition of
its algebra completion: the kernel of any weak-ideal stage projection. -/
theorem exists_isWeakIdealOfDefinition [IsWeaklyPreadmissibleRing A] :
    ∃ I : Ideal (weakIdealCompletion A A'), TopologicalRing.Ideal.IsWeakIdealOfDefinition I := by
  obtain ⟨I, hI⟩ := IsWeaklyPreadmissibleRing.exists_ideal_isWeakIdealOfDefinition (R := A)
  exact ⟨RingHom.ker (eval A A' hI), eval_ker_isWeakIdealOfDefinition A A' hI⟩

/-- Weak-ideal completion is weakly admissible already over a weakly
pre-admissible base. Completeness of the base is unnecessary. -/
theorem isWeaklyAdmissibleRing [IsWeaklyPreadmissibleRing A] :
    IsWeaklyAdmissibleRing (weakIdealCompletion A A') where
  toIsTopologicalRing := inferInstance
  toIsLinearTopology := inferInstance
  exists_ideal_isWeakIdealOfDefinition := exists_isWeakIdealOfDefinition A A'
  isT2 := inferInstance
  isComplete := completeSpace A A'

end weakIdealCompletion

end TopologicalRing
