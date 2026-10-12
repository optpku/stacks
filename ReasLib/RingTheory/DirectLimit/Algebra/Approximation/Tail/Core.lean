/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import ReasLib.RingTheory.DirectLimit.Tail.Colimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Core data for tails of directed algebra approximations

This leaf owns restriction of the source/target systems and of finite-type
approximation data to a cofinal tail.  Optional locality and essential-finite-
type transport is kept in `Tail.Properties`; colimit and base-change formulas
are separate leaves.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Hom

variable {f : R →+* S}

/-- Restrict a directed ring-hom approximation to the tail above one of its
stages. -/
@[stacks 00R1 "directed approximation tail"]
noncomputable def tail (A : Hom f) (i₀ : A.index) : Hom f where
  index := Set.Ici i₀
  preorder := inferInstance
  indexNonempty := inferInstance
  directedOrder := inferInstance
  source := fun j ↦ A.source j.1
  target := fun j ↦ A.target j.1
  sourceCommRing := fun _ ↦ inferInstance
  targetCommRing := fun _ ↦ inferInstance
  sourceMap := fun j k h ↦ A.sourceMap j.1 k.1 h
  targetMap := fun j k h ↦ A.targetMap j.1 k.1 h
  sourceDirectedSystem :=
    DirectedSystem.ici (fun i j h ↦ A.sourceMap i j h) i₀
  targetDirectedSystem :=
    DirectedSystem.ici (fun i j h ↦ A.targetMap i j h) i₀
  map := fun j ↦ A.map j.1
  map_comm := fun h ↦ A.map_comm h
  sourceColimit :=
    Ring.DirectLimit.Tail.equivTo (fun i j h ↦ A.sourceMap i j h) i₀ A.sourceColimit
  targetColimit :=
    Ring.DirectLimit.Tail.equivTo (fun i j h ↦ A.targetMap i j h) i₀ A.targetColimit
  colimit_comm := sorry

/-- The source family of a tail approximation is the original source family at
the underlying stages. -/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_source (A : Hom f) (i₀ : A.index) :
    (A.tail i₀).source = fun j : Set.Ici i₀ ↦ A.source j.1 := sorry

/-- The target family of a tail approximation is the original target family at
the underlying stages. -/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_target (A : Hom f) (i₀ : A.index) :
    (A.tail i₀).target = fun j : Set.Ici i₀ ↦ A.target j.1 := sorry

/-- The stage map of a tail approximation is the original stage map at the
underlying index. -/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_map (A : Hom f) (i₀ : A.index) (j : Set.Ici i₀) :
    (A.tail i₀).map j = A.map j.1 := sorry

/-- A source transition in a tail is the corresponding original transition. -/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_sourceMap (A : Hom f) (i₀ : A.index)
    {j k : Set.Ici i₀} (h : j ≤ k) :
    (A.tail i₀).sourceMap j k h = A.sourceMap j.1 k.1 h := sorry

/-- A target transition in a tail is the corresponding original transition. -/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_targetMap (A : Hom f) (i₀ : A.index)
    {j k : Set.Ici i₀} (h : j ≤ k) :
    (A.tail i₀).targetMap j k h = A.targetMap j.1 k.1 h := sorry

/-- The stage map of a tail approximation agrees pointwise with the original
stage map. -/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_map_apply (A : Hom f) (i₀ : A.index) (j : Set.Ici i₀)
    (x : A.source j.1) :
    (A.tail i₀).map j x = A.map j.1 x := sorry

/-- Source transitions in a tail agree pointwise with the original transitions.
-/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_sourceMap_apply (A : Hom f) (i₀ : A.index)
    {j k : Set.Ici i₀} (h : j ≤ k) (x : A.source j.1) :
    (A.tail i₀).sourceMap j k h x = A.sourceMap j.1 k.1 h x := sorry

/-- Target transitions in a tail agree pointwise with the original transitions.
-/
@[simp, stacks 00R1 "directed approximation tail"]
theorem tail_targetMap_apply (A : Hom f) (i₀ : A.index)
    {j k : Set.Ici i₀} (h : j ≤ k) (x : A.target j.1) :
    (A.tail i₀).targetMap j k h x = A.targetMap j.1 k.1 h x := sorry

/-- The source-stage map to the limit is unchanged after restricting an
approximation to a tail. -/
@[stacks 00R1 "directed approximation tail"]
theorem tail_sourceToLimit (A : Hom f) (i₀ : A.index) (j : Set.Ici i₀) :
    (A.tail i₀).sourceToLimit j = A.sourceToLimit j.1 := sorry

/-- The target-stage map to the limit is unchanged after restricting an
approximation to a tail. -/
@[stacks 00R1 "directed approximation tail"]
theorem tail_targetToLimit (A : Hom f) (i₀ : A.index) (j : Set.Ici i₀) :
    (A.tail i₀).targetToLimit j = A.targetToLimit j.1 := sorry

end Hom

namespace FiniteType

variable {f : R →+* S}

/-- Restrict a finite-type directed approximation to the tail above one of its
stages. -/
@[stacks 00R1 "finite-type approximation tail"]
noncomputable def tail (A : FiniteType f) (i₀ : A.index) : FiniteType f where
  toHom := A.toHom.tail i₀
  sourceFiniteType := fun j ↦ A.sourceFiniteType j.1
  mapFiniteType := fun j ↦ A.mapFiniteType j.1

/-- Forgetting finite-type data commutes with restricting to a tail. -/
@[simp, stacks 00R1 "finite-type approximation tail"]
theorem tail_toHom (A : FiniteType f) (i₀ : A.index) :
    (A.tail i₀).toHom = A.toHom.tail i₀ := sorry

/-- Source-stage finite type is preserved pointwise by taking a tail. -/
@[simp, stacks 00R1 "finite-type approximation tail"]
theorem tail_sourceFiniteType (A : FiniteType f) (i₀ : A.index)
    (j : Set.Ici i₀) :
    (A.tail i₀).sourceFiniteType j = A.sourceFiniteType j.1 := sorry

/-- Stage-map finite type is preserved pointwise by taking a tail. -/
@[simp, stacks 00R1 "finite-type approximation tail"]
theorem tail_mapFiniteType (A : FiniteType f) (i₀ : A.index)
    (j : Set.Ici i₀) :
    (A.tail i₀).mapFiniteType j = A.mapFiniteType j.1 := sorry

end FiniteType

end Ring.DirectLimit.Algebra.Approximation
