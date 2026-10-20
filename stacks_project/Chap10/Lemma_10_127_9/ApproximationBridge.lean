/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_127_9
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The reusable approximation view of the Chapter 10 owner

@stack 00QT

`DirectedLocalHomApproximation` is the source-facing Chapter 10 owner.  Its
data-preserving conversion to the neutral ReasLib owner
`Ring.DirectLimit.Algebra.Approximation.Hom` is defined with the owner in
`Lemma_10_127_9`.  This file transfers the essential-finite-type and locality
property bundles and provides the reverse source-facing view when those two
property layers are available.  It also exposes the source-facing view of a
cofinal tail, while ReasLib remains independent of the chapter.
-/

@[expose] public section

universe u v

namespace DirectedLocalHomApproximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Transfer the source-facing essential-finite-type hypotheses to the neutral
approximation property bundle. -/
@[stacks 00QT "legacy directed approximation bridge"]
instance toApproximation_essFiniteType
    (A : DirectedLocalHomApproximation f) :
    A.toApproximation.EssFiniteType where
  source := A.source_essFiniteType
  map := A.target_essFiniteType

/-- Transfer the source-facing local-ring and local-homomorphism conditions to
the neutral approximation locality bundle. -/
@[stacks 00QT "legacy directed approximation bridge"]
instance toApproximation_local
    (A : DirectedLocalHomApproximation f) :
    A.toApproximation.Local where
  source := A.instIsLocalRingRStage
  sourceMap := fun {i j} h ↦ A.map_isLocalHom i j h
  target := A.instIsLocalRingSStage
  map := A.stageMap_isLocalHom
  targetMap := fun {i j} h ↦ A.targetMap_isLocalHom i j h

/-- A neutral directed approximation carrying the local and
essential-finite-type property layers, viewed through the Chapter 10
source-facing owner.  This is a data-preserving bridge for source-facing
constructions that need the local stage structures explicitly. -/
@[stacks 00QT "legacy directed approximation bridge"]
noncomputable def ofApproximation
    (A : Ring.DirectLimit.Algebra.Approximation.Hom f)
    [A.Local] [A.EssFiniteType] :
    DirectedLocalHomApproximation f where
  Λ := A.index
  instPreorder := A.preorder
  instNonempty := A.indexNonempty
  instDirectedOrder := A.directedOrder
  RStage := A.source
  instCommRingRStage := A.sourceCommRing
  map := A.sourceMap
  instDirectedSystemRStage := A.sourceDirectedSystem
  colimitIso := A.sourceColimit
  instIsLocalRingRStage :=
    fun i ↦ Ring.DirectLimit.Algebra.Approximation.Hom.Local.source (A := A) i
  map_isLocalHom := fun _ _ h ↦
    Ring.DirectLimit.Algebra.Approximation.Hom.Local.sourceMap (A := A) h
  SStage := A.target
  instCommRingSStage := A.targetCommRing
  instIsLocalRingSStage :=
    fun i ↦ Ring.DirectLimit.Algebra.Approximation.Hom.Local.target (A := A) i
  stageMap := A.map
  stageMap_isLocalHom :=
    fun i ↦ Ring.DirectLimit.Algebra.Approximation.Hom.Local.map (A := A) i
  targetMap := A.targetMap
  targetMap_isLocalHom := fun _ _ h ↦
    Ring.DirectLimit.Algebra.Approximation.Hom.Local.targetMap (A := A) h
  instDirectedSystemTarget := A.targetDirectedSystem
  comm := fun h ↦ A.map_comm h
  targetColimit := A.targetColimit
  colimit_comm := A.colimit_comm
  source_essFiniteType :=
    fun i ↦ Ring.DirectLimit.Algebra.Approximation.Hom.EssFiniteType.source (A := A) i
  target_essFiniteType :=
    fun i ↦ Ring.DirectLimit.Algebra.Approximation.Hom.EssFiniteType.map (A := A) i

/-- Restrict a source-facing local approximation to a cofinal tail.  The
directed-system and colimit data are owned by the neutral `Hom.tail`; this
bridge retains the explicit local stage structures required by Chapter 10
module approximations. -/
@[stacks 00QT "legacy directed approximation bridge"]
noncomputable def tail (A : DirectedLocalHomApproximation f) (i₀ : A.Λ) :
    DirectedLocalHomApproximation f :=
  ofApproximation (A.toApproximation.tail i₀)

/-- The target-stage map to the final ring is unchanged by the source-facing
tail bridge.  This is the Chapter 10 view of `Hom.tail_targetToLimit`. -/
@[stacks 00QT "legacy directed approximation bridge"]
theorem tail_targetToLimit
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ) (j : Set.Ici i₀) :
    targetStageToLimitHom (A.tail i₀) j = targetStageToLimitHom A j.1 := sorry

end DirectedLocalHomApproximation

#check @DirectedLocalHomApproximation.toApproximation
#check @DirectedLocalHomApproximation.toApproximation_essFiniteType
#check @DirectedLocalHomApproximation.toApproximation_local
#check @DirectedLocalHomApproximation.ofApproximation
#check @DirectedLocalHomApproximation.tail
#check @DirectedLocalHomApproximation.tail_targetToLimit
#check @Ring.DirectLimit.Algebra.Approximation.Hom.tail
#check @Ring.DirectLimit.Algebra.Approximation.Hom.tail_targetToLimit
#print axioms DirectedLocalHomApproximation.toApproximation
#print axioms DirectedLocalHomApproximation.toApproximation_essFiniteType
#print axioms DirectedLocalHomApproximation.toApproximation_local
#print axioms DirectedLocalHomApproximation.ofApproximation
#print axioms DirectedLocalHomApproximation.tail
