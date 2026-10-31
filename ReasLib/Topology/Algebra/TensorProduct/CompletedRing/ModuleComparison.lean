/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing
public import ReasLib.Topology.Algebra.TensorProduct.Completion

/-!
# Ring-level versus module-level completed tensor products

For linearly topologized `R`-algebras `A` and `B`, the completed tensor product
`A ⊗̂_R B` of Stacks 0AMU is the module-level object `TensorProduct.Completed R A B`, the inverse
limit of `(A ⧸ U) ⊗[R] (B ⧸ V)` over open `R`-submodules. The ring-level carrier
`Algebra.TensorProduct.Completed R A B` takes the same limit over the cofinal subsystem of open
ideals, which is what makes its pointwise ring structure available.

This file records the comparison: restriction to ideal stages, with the inverse obtained by
choosing an open ideal below each open submodule and pushing down along the quotient maps.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Topology

universe u

namespace Algebra.TensorProduct.Completed

variable (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [TopologicalSpace A] [TopologicalSpace B]

/-- An ideal regarded as an `R`-submodule of the algebra. -/
abbrev idealSubmodule {S : Type u} [CommRing S] [Algebra R S] (I : Ideal S) : Submodule R S :=
  I.restrictScalars R

/-- Every open `R`-submodule of a linearly topologized algebra contains an open ideal. -/
theorem exists_openIdeal_le {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]
    (U : Submodule R S) (hU : IsOpen (U : Set S)) :
    ∃ I : Ideal S, IsOpen (I : Set S) ∧ idealSubmodule R I ≤ U := by
  obtain ⟨I, hI, hIU⟩ :=
    (IsLinearTopology.hasBasis_open_ideal (R := S)).mem_iff.mp (hU.mem_nhds (zero_mem U))
  exact ⟨I, hI, hIU⟩

/-- A chosen open ideal contained in an open `R`-submodule. -/
def openIdealBelow {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]
    (U : {U : Submodule R S // IsOpen (U : Set S)}) : {I : Ideal S // IsOpen (I : Set S)} :=
  ⟨(exists_openIdeal_le R U.1 U.2).choose, (exists_openIdeal_le R U.1 U.2).choose_spec.1⟩

theorem idealSubmodule_openIdealBelow_le {S : Type u} [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    (U : {U : Submodule R S // IsOpen (U : Set S)}) :
    idealSubmodule R (openIdealBelow R U).1 ≤ U.1 :=
  (exists_openIdeal_le R U.1 U.2).choose_spec.2

/-- The `R`-linear map `S ⧸ U ← S ⧸ I` for an ideal `I` whose underlying submodule lies
in `U`. -/
def stageFactor {S : Type u} [CommRing S] [Algebra R S] {I : Ideal S} {U : Submodule R S}
    (h : idealSubmodule R I ≤ U) : (S ⧸ I) →ₗ[R] S ⧸ U :=
  (Submodule.factor h).comp (Submodule.Quotient.restrictScalarsEquiv R I).symm.toLinearMap

/-- Evaluation of `stageFactor` on a quotient representative. -/
theorem stageFactor_apply_mk {S : Type u} [CommRing S] [Algebra R S]
    {I : Ideal S} {U : Submodule R S} (h : idealSubmodule R I ≤ U) (x : S) :
    stageFactor R h (Submodule.Quotient.mk (p := idealSubmodule R I) x) =
      Submodule.Quotient.mk (p := U) x := by
  rfl

/-- Factoring through an intermediate ideal does not change the quotient map. -/
theorem stageFactor_comp {S : Type u} [CommRing S] [Algebra R S]
    {I J : Ideal S} {U : Submodule R S} (hIJ : I ≤ J)
    (hJU : idealSubmodule R J ≤ U) :
    (stageFactor R hJU).comp (Ideal.Quotient.factorₐ R hIJ).toLinearMap =
      stageFactor R (fun _ hx => hJU (hIJ hx)) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- A further quotient of the target commutes with `stageFactor`. -/
theorem factor_comp_stageFactor {S : Type u} [CommRing S] [Algebra R S]
    {I : Ideal S} {U V : Submodule R S} (hIU : idealSubmodule R I ≤ U) (hUV : U ≤ V) :
    (Submodule.factor hUV).comp (stageFactor R hIU) = stageFactor R (hIU.trans hUV) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- Stage tensor maps commute with refinement of the two open ideals. -/
theorem stageFactors_mapFactor {I I' : Ideal A} {J J' : Ideal B}
    {U : Submodule R A} {V : Submodule R B}
    (hII' : I ≤ I') (hJJ' : J ≤ J')
    (hIU : idealSubmodule R I' ≤ U) (hJV : idealSubmodule R J' ≤ V)
    (z : (A ⧸ I) ⊗[R] (B ⧸ J)) :
    _root_.TensorProduct.map (stageFactor R hIU) (stageFactor R hJV)
      (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hII')
        (Ideal.Quotient.factorₐ R hJJ') z) =
    _root_.TensorProduct.map (stageFactor R (fun _ hx => hIU (hII' hx)))
      (stageFactor R (fun _ hx => hJV (hJJ' hx))) z := by
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A linearly topologized `R`-algebra is linearly topologized as an `R`-module: its open ideals
form a basis of open `R`-submodules at zero. -/
theorem isLinearTopology_of_algebra (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsLinearTopology S S] : IsLinearTopology R S :=
  IsLinearTopology.mk_of_hasBasis' R (S := Ideal S) (IsLinearTopology.hasBasis_ideal (R := S))
    fun I r m hm ↦ by
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ hm

attribute [local instance] isLinearTopology_of_algebra

variable [IsTopologicalRing A] [IsTopologicalRing B]
variable [IsLinearTopology A A] [IsLinearTopology B B]

/-- An open ideal of a topological ring is an open `R`-submodule. -/
theorem isOpen_idealSubmodule {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S]
    (I : {I : Ideal S // IsOpen (I : Set S)}) : IsOpen (idealSubmodule R I.1 : Set S) :=
  I.2

/-- Restriction of a compatible family over open submodules to the open-ideal stages. -/
def toRingStage (f : _root_.TensorProduct.Completed R A B)
    (I : {I : Ideal A // IsOpen (I : Set A)}) (J : {J : Ideal B // IsOpen (J : Set B)}) :
    (A ⧸ I.1) ⊗[R] (B ⧸ J.1) :=
  _root_.TensorProduct.map (Submodule.Quotient.restrictScalarsEquiv R I.1).toLinearMap
    (Submodule.Quotient.restrictScalarsEquiv R J.1).toLinearMap
    (f.1 ⟨idealSubmodule R I.1, isOpen_idealSubmodule R I⟩
      ⟨idealSubmodule R J.1, isOpen_idealSubmodule R J⟩)

/-- Extension of a compatible family over open-ideal stages to all open submodule stages, via
a chosen open ideal below each open submodule. The value does not depend on that choice by
compatibility of the family. -/
def toModuleStage (g : Completed R A B)
    (U : {U : Submodule R A // IsOpen (U : Set A)}) (V : {V : Submodule R B // IsOpen (V : Set B)}) :
    (A ⧸ U.1) ⊗[R] (B ⧸ V.1) :=
  _root_.TensorProduct.map (stageFactor R (idealSubmodule_openIdealBelow_le R U))
    (stageFactor R (idealSubmodule_openIdealBelow_le R V))
    (g.1 (openIdealBelow R U) (openIdealBelow R V))

/-- The extension to submodule stages can be computed using any smaller open ideals. -/
theorem toModuleStage_independent (g : Completed R A B)
    (U : {U : Submodule R A // IsOpen (U : Set A)})
    (V : {V : Submodule R B // IsOpen (V : Set B)})
    (I : {I : Ideal A // IsOpen (I : Set A)})
    (J : {J : Ideal B // IsOpen (J : Set B)})
    (hIU : idealSubmodule R I.1 ≤ U.1) (hJV : idealSubmodule R J.1 ≤ V.1) :
    toModuleStage R A B g U V =
      _root_.TensorProduct.map (stageFactor R hIU) (stageFactor R hJV) (g.1 I J) := by
  let K : {I : Ideal A // IsOpen (I : Set A)} :=
    ⟨(openIdealBelow R U).1 ⊓ I.1, (openIdealBelow R U).2.inter I.2⟩
  let L : {J : Ideal B // IsOpen (J : Set B)} :=
    ⟨(openIdealBelow R V).1 ⊓ J.1, (openIdealBelow R V).2.inter J.2⟩
  have hc := g.2 K (openIdealBelow R U) L (openIdealBelow R V)
    (show K.1 ≤ (openIdealBelow R U).1 from inf_le_left)
    (show L.1 ≤ (openIdealBelow R V).1 from inf_le_left)
  have hi := g.2 K I L J (show K.1 ≤ I.1 from inf_le_right)
    (show L.1 ≤ J.1 from inf_le_right)
  unfold toModuleStage
  rw [← hc, ← hi, stageFactors_mapFactor, stageFactors_mapFactor]

/-- The extended submodule stages form a compatible inverse-limit family. -/
theorem toModuleStage_compatible (g : Completed R A B)
    (U U' : {U : Submodule R A // IsOpen (U : Set A)})
    (V V' : {V : Submodule R B // IsOpen (V : Set B)})
    (hUU' : U.1 ≤ U'.1) (hVV' : V.1 ≤ V'.1) :
    _root_.TensorProduct.map (Submodule.factor hUU') (Submodule.factor hVV')
      (toModuleStage R A B g U V) = toModuleStage R A B g U' V' := by
  rw [toModuleStage_independent R A B g U' V' (openIdealBelow R U) (openIdealBelow R V)
    ((idealSubmodule_openIdealBelow_le R U).trans hUU')
    ((idealSubmodule_openIdealBelow_le R V).trans hVV')]
  unfold toModuleStage
  rw [_root_.TensorProduct.map_map, factor_comp_stageFactor, factor_comp_stageFactor]

/-- Restricting a compatible submodule family gives compatible ideal stages. -/
theorem toRingStage_compatible (f : _root_.TensorProduct.Completed R A B)
    (I I' : {I : Ideal A // IsOpen (I : Set A)})
    (J J' : {J : Ideal B // IsOpen (J : Set B)})
    (hII' : I.1 ≤ I'.1) (hJJ' : J.1 ≤ J'.1) :
    Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hII') (Ideal.Quotient.factorₐ R hJJ')
      (toRingStage R A B f I J) = toRingStage R A B f I' J' := by
  unfold toRingStage
  rw [← f.2 ⟨idealSubmodule R I.1, I.2⟩ ⟨idealSubmodule R I'.1, I'.2⟩
    ⟨idealSubmodule R J.1, J.2⟩ ⟨idealSubmodule R J'.1, J'.2⟩ hII' hJJ']
  generalize f.1 ⟨idealSubmodule R I.1, I.2⟩ ⟨idealSubmodule R J.1, J.2⟩ = z
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (idealSubmodule R I.1) x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (idealSubmodule R J.1) y
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

omit [IsTopologicalRing A] [IsTopologicalRing B] [IsLinearTopology A A] [IsLinearTopology B B] in
/-- The algebra scalar action on the completed ring is pointwise on its stages. -/
theorem stage_smul (r : R) (g : Completed R A B)
    (I : {I : Ideal A // IsOpen (I : Set A)})
    (J : {J : Ideal B // IsOpen (J : Set B)}) :
    (r • g).1 I J = r • g.1 I J := by
  change (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.1)
    (Ideal.Quotient.mkₐ R J.1) (algebraMap R (A ⊗[R] B) r)) * g.1 I J = _
  rw [AlgHom.commutes, Algebra.smul_def]

/-- The canonical `R`-linear identification of the ring-level completed tensor product (limit
over open ideals) with the module-level completed tensor product of Stacks 0AMU (limit over open
`R`-submodules). -/
def equivModuleCompleted : Completed R A B ≃ₗ[R] _root_.TensorProduct.Completed R A B where
  toFun g := ⟨toModuleStage R A B g, toModuleStage_compatible R A B g⟩
  invFun f := ⟨toRingStage R A B f, toRingStage_compatible R A B f⟩
  left_inv := by
    intro g
    apply Subtype.ext
    funext I J
    change _root_.TensorProduct.map
      (Submodule.Quotient.restrictScalarsEquiv R I.1).toLinearMap
      (Submodule.Quotient.restrictScalarsEquiv R J.1).toLinearMap
      (toModuleStage R A B g ⟨idealSubmodule R I.1, I.2⟩
        ⟨idealSubmodule R J.1, J.2⟩) = g.1 I J
    rw [toModuleStage_independent R A B g _ _ I J le_rfl le_rfl]
    generalize g.1 I J = z
    induction z using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  right_inv := by
    intro f
    apply Subtype.ext
    funext U V
    change _root_.TensorProduct.map
      (stageFactor R (idealSubmodule_openIdealBelow_le R U))
      (stageFactor R (idealSubmodule_openIdealBelow_le R V))
      (toRingStage R A B f (openIdealBelow R U) (openIdealBelow R V)) = f.1 U V
    unfold toRingStage
    rw [← f.2 ⟨idealSubmodule R (openIdealBelow R U).1, (openIdealBelow R U).2⟩ U
      ⟨idealSubmodule R (openIdealBelow R V).1, (openIdealBelow R V).2⟩ V
      (idealSubmodule_openIdealBelow_le R U) (idealSubmodule_openIdealBelow_le R V)]
    generalize f.1 ⟨idealSubmodule R (openIdealBelow R U).1, (openIdealBelow R U).2⟩
      ⟨idealSubmodule R (openIdealBelow R V).1, (openIdealBelow R V).2⟩ = z
    induction z using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (idealSubmodule R (openIdealBelow R U).1) x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (idealSubmodule R (openIdealBelow R V).1) y
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_add' := by
    intro g h
    apply Subtype.ext
    funext U V
    change _root_.TensorProduct.map _ _ (g.1 _ _ + h.1 _ _) =
      _root_.TensorProduct.map _ _ (g.1 _ _) + _root_.TensorProduct.map _ _ (h.1 _ _)
    exact LinearMap.map_add _ _ _
  map_smul' := by
    intro r g
    apply Subtype.ext
    funext U V
    change toModuleStage R A B (r • g) U V = r • toModuleStage R A B g U V
    unfold toModuleStage
    rw [stage_smul]
    exact LinearMap.map_smul _ _ _

/-- On the stage of open submodules coming from open ideals, the comparison is the stage
identification `A ⧸ I ≅ A ⧸ I` of quotients by an ideal and by its underlying submodule. -/
theorem π_equivModuleCompleted (g : Completed R A B)
    (I : {I : Ideal A // IsOpen (I : Set A)}) (J : {J : Ideal B // IsOpen (J : Set B)}) :
    _root_.TensorProduct.Completed.π R A B (idealSubmodule R I.1) (idealSubmodule R J.1)
        (isOpen_idealSubmodule R I) (isOpen_idealSubmodule R J) (equivModuleCompleted R A B g) =
      _root_.TensorProduct.map
        (Submodule.Quotient.restrictScalarsEquiv R I.1).symm.toLinearMap
        (Submodule.Quotient.restrictScalarsEquiv R J.1).symm.toLinearMap
        (π R A B I.1 J.1 I.2 J.2 g) := by
  change toModuleStage R A B g ⟨idealSubmodule R I.1, I.2⟩
    ⟨idealSubmodule R J.1, J.2⟩ = _root_.TensorProduct.map _ _ (g.1 I J)
  rw [toModuleStage_independent R A B g _ _ I J le_rfl le_rfl]
  have hI : stageFactor R (le_rfl : idealSubmodule R I.1 ≤ idealSubmodule R I.1) =
      (Submodule.Quotient.restrictScalarsEquiv R I.1).symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hJ : stageFactor R (le_rfl : idealSubmodule R J.1 ≤ idealSubmodule R J.1) =
      (Submodule.Quotient.restrictScalarsEquiv R J.1).symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [hI, hJ]

/-- The comparison is compatible with the canonical maps from the algebraic tensor product. -/
theorem equivModuleCompleted_of (x : A ⊗[R] B) :
    equivModuleCompleted R A B (of R A B x) =
      _root_.TensorProduct.Completed.of R A B
        ((_root_.TensorProduct.Linear.equiv R A B).symm x) := by
  apply Subtype.ext
  funext U V
  change _root_.TensorProduct.map
    (stageFactor R (idealSubmodule_openIdealBelow_le R U))
    (stageFactor R (idealSubmodule_openIdealBelow_le R V))
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (openIdealBelow R U).1)
      (Ideal.Quotient.mkₐ R (openIdealBelow R V).1) x) =
    _root_.TensorProduct.map U.1.mkQ V.1.mkQ
      ((_root_.TensorProduct.Linear.equiv R A B)
        ((_root_.TensorProduct.Linear.equiv R A B).symm x))
  rw [LinearEquiv.apply_symm_apply]
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A coordinate of a compatible family is continuous for the inverse-limit topology. -/
private theorem continuous_coordinate {ι κ : Type u} {S : ι → κ → Type u}
    {P : (∀ i j, S i j) → Prop} (i : ι) (j : κ) :
    Continuous[TopologicalSpace.induced Subtype.val
      (⨅ (i : ι) (j : κ), TopologicalSpace.induced (fun f : ∀ i j, S i j => f i j)
        (⊥ : TopologicalSpace (S i j))), ⊥]
      (fun f : {f : ∀ i j, S i j // P f} => f.1 i j) := by
  apply continuous_iff_le_induced.mpr
  have h : (⨅ (i : ι) (j : κ), TopologicalSpace.induced
      (fun f : ∀ i j, S i j => f i j) (⊥ : TopologicalSpace (S i j))) ≤
      TopologicalSpace.induced (fun f : ∀ i j, S i j => f i j) ⊥ :=
    (iInf_le _ i).trans (iInf_le _ j)
  simpa only [induced_compose, Function.comp_def] using
    (induced_mono (g := (Subtype.val : {f : ∀ i j, S i j // P f} → _)) h)

/-- The comparison is continuous. -/
theorem continuous_equivModuleCompleted : Continuous (equivModuleCompleted R A B) := by
  apply continuous_induced_rng.mpr
  apply continuous_iInf_rng.mpr
  intro U
  apply continuous_iInf_rng.mpr
  intro V
  apply continuous_induced_rng.mpr
  letI : TopologicalSpace ((A ⧸ (openIdealBelow R U).1) ⊗[R]
    (B ⧸ (openIdealBelow R V).1)) := ⊥
  letI : TopologicalSpace ((A ⧸ U.1) ⊗[R] (B ⧸ V.1)) := ⊥
  have hc : @Continuous (Completed R A B) _ inferInstance ⊥
      (fun g => g.1 (openIdealBelow R U) (openIdealBelow R V)) :=
    continuous_coordinate (openIdealBelow R U) (openIdealBelow R V)
  exact (show @Continuous _ _ ⊥ ⊥
    (_root_.TensorProduct.map (stageFactor R (idealSubmodule_openIdealBelow_le R U))
      (stageFactor R (idealSubmodule_openIdealBelow_le R V))) from continuous_bot).comp hc

/-- The inverse comparison is continuous. -/
theorem continuous_equivModuleCompleted_symm :
    Continuous (equivModuleCompleted R A B).symm := by
  apply continuous_induced_rng.mpr
  apply continuous_iInf_rng.mpr
  intro I
  apply continuous_iInf_rng.mpr
  intro J
  apply continuous_induced_rng.mpr
  letI : TopologicalSpace ((A ⧸ idealSubmodule R I.1) ⊗[R]
    (B ⧸ idealSubmodule R J.1)) := ⊥
  letI : TopologicalSpace ((A ⧸ I.1) ⊗[R] (B ⧸ J.1)) := ⊥
  have hc : @Continuous (_root_.TensorProduct.Completed R A B) _ inferInstance ⊥
      (fun f => f.1 ⟨idealSubmodule R I.1, I.2⟩ ⟨idealSubmodule R J.1, J.2⟩) :=
    continuous_coordinate
      (S := fun (U : {U : Submodule R A // IsOpen (U : Set A)})
        (V : {V : Submodule R B // IsOpen (V : Set B)}) => (A ⧸ U.1) ⊗[R] (B ⧸ V.1))
      (P := fun f => ∀ (U U' : {U : Submodule R A // IsOpen (U : Set A)})
        (V V' : {V : Submodule R B // IsOpen (V : Set B)})
        (hU : U.1 ≤ U'.1) (hV : V.1 ≤ V'.1),
        _root_.TensorProduct.map (Submodule.factor (R := R) hU)
          (Submodule.factor (R := R) hV)
          (f U V) = f U' V')
      ⟨idealSubmodule R I.1, I.2⟩ ⟨idealSubmodule R J.1, J.2⟩
  exact (show @Continuous _ _ ⊥ ⊥
    (_root_.TensorProduct.map (Submodule.Quotient.restrictScalarsEquiv R I.1).toLinearMap
      (Submodule.Quotient.restrictScalarsEquiv R J.1).toLinearMap) from continuous_bot).comp hc

end Algebra.TensorProduct.Completed
