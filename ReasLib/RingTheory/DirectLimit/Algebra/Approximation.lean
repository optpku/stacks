module

public import ReasLib.RingTheory.DirectLimit.Comparison
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed approximations of commutative-ring homomorphisms

This leaf owns the reusable data of a compatible directed system of
commutative-ring homomorphisms whose two direct limits recover a fixed map.
Finite-type conditions and stagewise base-change conditions are separate
layers, so applications can use the underlying approximation without carrying
unneeded finiteness hypotheses.
-/

@[expose] public section

universe uR uS uI uSrc uTgt

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-
The index and stage carrier universes are intentionally independent of the
limiting ring universes.  They occur together in the universe of the direct
limit carrier, so the universe linter cannot recognize this useful generality.
-/
set_option linter.checkUnivs false in
/-- A compatible directed presentation of a commutative-ring homomorphism by
stagewise ring homomorphisms.  The source and target systems, their transition
maps, and their identifications with the limiting rings are primitive data. -/
@[stacks 00R0 "directed ring-hom approximation"]
structure Hom (f : R →+* S) where
  /-- The directed index type. -/
  index : Type uI
  /-- The order on approximation stages. -/
  preorder : Preorder index
  /-- The directed system has a stage. -/
  indexNonempty : Nonempty index
  /-- Every two stages admit a common later stage. -/
  directedOrder : IsDirectedOrder index
  /-- The source ring at each approximation stage. -/
  source : index → Type uSrc
  /-- The target ring at each approximation stage. -/
  target : index → Type uTgt
  /-- The commutative-ring structure on each source stage. -/
  sourceCommRing (i : index) : CommRing (source i)
  /-- The commutative-ring structure on each target stage. -/
  targetCommRing (i : index) : CommRing (target i)
  /-- The transition map between source stages. -/
  sourceMap (i j : index) (h : i ≤ j) : source i →+* source j
  /-- The transition map between target stages. -/
  targetMap (i j : index) (h : i ≤ j) : target i →+* target j
  /-- The source transition maps form a directed system. -/
  sourceDirectedSystem : DirectedSystem source (sourceMap · · ·)
  /-- The target transition maps form a directed system. -/
  targetDirectedSystem : DirectedSystem target (targetMap · · ·)
  /-- The ring homomorphism at each approximation stage. -/
  map (i : index) : source i →+* target i
  /-- The stagewise maps commute with both transition systems. -/
  map_comm {i j : index} (h : i ≤ j) :
    (map j).comp (sourceMap i j h) = (targetMap i j h).comp (map i)
  /-- The source direct limit is identified with the source of the limiting map. -/
  sourceColimit :
    Ring.DirectLimit source (fun i j h ↦ sourceMap i j h) ≃+* R
  /-- The target direct limit is identified with the target of the limiting map. -/
  targetColimit :
    Ring.DirectLimit target (fun i j h ↦ targetMap i j h) ≃+* S
  /-- The map induced on direct limits is the prescribed limiting map. -/
  colimit_comm :
    targetColimit.toRingHom.comp (Ring.DirectLimit.map map (fun _ _ h ↦ map_comm h)) =
      f.comp sourceColimit.toRingHom

attribute [instance] Hom.preorder
attribute [instance] Hom.indexNonempty
attribute [instance] Hom.directedOrder
attribute [instance] Hom.sourceCommRing
attribute [instance] Hom.targetCommRing
attribute [instance] Hom.sourceDirectedSystem
attribute [instance] Hom.targetDirectedSystem

set_option linter.checkUnivs false in
/-- A directed ring-hom approximation whose source stages are finite type over
`ℤ` and whose stage maps are finite type. -/
@[stacks 00R0 "finite-type ring-hom approximation"]
structure FiniteType (f : R →+* S) extends Hom f where
  /-- Each source stage is finite type over `ℤ`. -/
  sourceFiniteType (i : index) : (Int.castRingHom (source i)).FiniteType
  /-- Each stagewise map from source to target is finite type. -/
  mapFiniteType (i : index) : (map i).FiniteType

namespace FiniteType

variable {f : R →+* S}

/-- The two finite-type conditions attached to one approximation stage. -/
@[stacks 00R0 "finite-type ring-hom approximation"]
theorem stage_spec (A : FiniteType f) (i : A.index) :
    (Int.castRingHom (A.source i)).FiniteType ∧
      (A.map i).FiniteType := sorry

end FiniteType

namespace Hom

variable {f : R →+* S}

/-- The canonical ring homomorphism from a source stage to the limiting source
ring. -/
@[stacks 00R0 "directed ring-hom approximation"]
noncomputable def sourceToLimit (A : Hom f) (i : A.index) : A.source i →+* R :=
  Ring.DirectLimit.toLimitHom
    A.source (fun i j h ↦ A.sourceMap i j h) A.sourceColimit i

/-- The canonical ring homomorphism from a target stage to the limiting target
ring. -/
@[stacks 00R0 "directed ring-hom approximation"]
noncomputable def targetToLimit (A : Hom f) (i : A.index) : A.target i →+* S :=
  Ring.DirectLimit.toLimitHom
    A.target (fun i j h ↦ A.targetMap i j h) A.targetColimit i

/-- The source transition at a stage is the identity ring homomorphism. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem sourceMap_id (A : Hom f) (i : A.index) :
    A.sourceMap i i le_rfl = RingHom.id (A.source i) := sorry

/-- Source transitions compose as the transition at the transitive order
relation.  This bundled form is the naturality API for composing stage maps. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem sourceMap_comp (A : Hom f) {i j k : A.index}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (A.sourceMap j k hjk).comp (A.sourceMap i j hij) =
      A.sourceMap i k (hij.trans hjk) := sorry

/-- The source transition identity law in pointwise form. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem sourceMap_id_apply (A : Hom f) (i : A.index) (x : A.source i) :
    A.sourceMap i i le_rfl x = x := sorry

/-- The source transition composition law in pointwise form. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem sourceMap_comp_apply (A : Hom f) {i j k : A.index}
    (hij : i ≤ j) (hjk : j ≤ k) (x : A.source i) :
    A.sourceMap j k hjk (A.sourceMap i j hij x) =
      A.sourceMap i k (hij.trans hjk) x := sorry

/-- The target transition at a stage is the identity ring homomorphism. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem targetMap_id (A : Hom f) (i : A.index) :
    A.targetMap i i le_rfl = RingHom.id (A.target i) := sorry

/-- Target transitions compose as the transition at the transitive order
relation. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem targetMap_comp (A : Hom f) {i j k : A.index}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (A.targetMap j k hjk).comp (A.targetMap i j hij) =
      A.targetMap i k (hij.trans hjk) := sorry

/-- The target transition identity law in pointwise form. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem targetMap_id_apply (A : Hom f) (i : A.index) (x : A.target i) :
    A.targetMap i i le_rfl x = x := sorry

/-- The target transition composition law in pointwise form. -/
@[simp, stacks 00R0 "directed ring-hom approximation transition"]
theorem targetMap_comp_apply (A : Hom f) {i j k : A.index}
    (hij : i ≤ j) (hjk : j ≤ k) (x : A.target i) :
    A.targetMap j k hjk (A.targetMap i j hij x) =
      A.targetMap i k (hij.trans hjk) x := sorry

end Hom

end Ring.DirectLimit.Algebra.Approximation
