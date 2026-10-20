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

/-- The canonical `R`-linear identification of the ring-level completed tensor product (limit
over open ideals) with the module-level completed tensor product of Stacks 0AMU (limit over open
`R`-submodules). -/
def equivModuleCompleted : Completed R A B ≃ₗ[R] _root_.TensorProduct.Completed R A B where
  toFun g := ⟨toModuleStage R A B g, sorry⟩
  invFun f := ⟨toRingStage R A B f, sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- On the stage of open submodules coming from open ideals, the comparison is the stage
identification `A ⧸ I ≅ A ⧸ I` of quotients by an ideal and by its underlying submodule. -/
theorem π_equivModuleCompleted (g : Completed R A B)
    (I : {I : Ideal A // IsOpen (I : Set A)}) (J : {J : Ideal B // IsOpen (J : Set B)}) :
    _root_.TensorProduct.Completed.π R A B (idealSubmodule R I.1) (idealSubmodule R J.1)
        (isOpen_idealSubmodule R I) (isOpen_idealSubmodule R J) (equivModuleCompleted R A B g) =
      _root_.TensorProduct.map
        (Submodule.Quotient.restrictScalarsEquiv R I.1).symm.toLinearMap
        (Submodule.Quotient.restrictScalarsEquiv R J.1).symm.toLinearMap
        (π R A B I.1 J.1 I.2 J.2 g) := sorry

/-- The comparison is compatible with the canonical maps from the algebraic tensor product. -/
theorem equivModuleCompleted_of (x : A ⊗[R] B) :
    equivModuleCompleted R A B (of R A B x) =
      _root_.TensorProduct.Completed.of R A B
        ((_root_.TensorProduct.Linear.equiv R A B).symm x) := sorry

/-- The comparison is continuous. -/
theorem continuous_equivModuleCompleted : Continuous (equivModuleCompleted R A B) := sorry

/-- The inverse comparison is continuous. -/
theorem continuous_equivModuleCompleted_symm :
    Continuous (equivModuleCompleted R A B).symm := sorry

end Algebra.TensorProduct.Completed
