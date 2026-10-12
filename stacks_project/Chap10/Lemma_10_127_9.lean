/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Core

@[expose] public section

/-!
# Directed approximation of local homomorphisms

@stack 00QT

The reusable directed-system data are owned by
`Ring.DirectLimit.Algebra.Approximation.Hom`.  This file retains the
source-facing local and essential-finite-type package used by the Chapter 10
approximation sequence, together with a data-preserving conversion to that
neutral owner.
-/

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.127.9 support: a directed approximation of a local ring homomorphism by local maps
whose source stages are essentially of finite type over `ℤ` and whose target stages are
essentially of finite type over the corresponding source stages.  The primitive stage and
colimit data agree with `Ring.DirectLimit.Algebra.Approximation.Hom`; the additional fields are
the source-facing locality and essential-finiteness hypotheses used in Chapter 10. -/
@[stacks 00QT "source-facing local directed approximation"]
structure DirectedLocalHomApproximation (f : R →+* S) where
  Λ : Type w
  instPreorder : Preorder Λ
  instNonempty : Nonempty Λ
  instDirectedOrder : IsDirectedOrder Λ
  RStage : Λ → Type u
  instCommRingRStage (i : Λ) : CommRing (RStage i)
  map (i j : Λ) (h : i ≤ j) : RStage i →+* RStage j
  instDirectedSystemRStage : DirectedSystem RStage (fun i j h ↦ map i j h)
  colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R
  instIsLocalRingRStage (i : Λ) : IsLocalRing (RStage i)
  map_isLocalHom (i j : Λ) (h : i ≤ j) : IsLocalHom (map i j h)
  SStage : Λ → Type v
  instCommRingSStage (i : Λ) : CommRing (SStage i)
  instIsLocalRingSStage (i : Λ) : IsLocalRing (SStage i)
  stageMap (i : Λ) : RStage i →+* SStage i
  stageMap_isLocalHom (i : Λ) : IsLocalHom (stageMap i)
  targetMap (i j : Λ) (h : i ≤ j) : SStage i →+* SStage j
  targetMap_isLocalHom (i j : Λ) (h : i ≤ j) : IsLocalHom (targetMap i j h)
  instDirectedSystemTarget : DirectedSystem SStage (fun i j h ↦ targetMap i j h)
  comm {i j : Λ} (h : i ≤ j) :
    (stageMap j).comp (map i j h) = (targetMap i j h).comp (stageMap i)
  targetColimit : Ring.DirectLimit SStage (fun i j h ↦ targetMap i j h) ≃+* S
  colimit_comm :
    targetColimit.toRingHom.comp (Ring.DirectLimit.map stageMap (fun _ _ h ↦ comm h)) =
      f.comp colimitIso.toRingHom
  source_essFiniteType (i : Λ) : (Int.castRingHom (RStage i)).EssFiniteType
  target_essFiniteType (i : Λ) : (stageMap i).EssFiniteType

attribute [instance] DirectedLocalHomApproximation.instPreorder
attribute [instance] DirectedLocalHomApproximation.instNonempty
attribute [instance] DirectedLocalHomApproximation.instDirectedOrder
attribute [instance] DirectedLocalHomApproximation.instCommRingRStage
attribute [instance] DirectedLocalHomApproximation.instDirectedSystemRStage
attribute [instance] DirectedLocalHomApproximation.instIsLocalRingRStage
attribute [instance] DirectedLocalHomApproximation.map_isLocalHom
attribute [instance] DirectedLocalHomApproximation.instCommRingSStage
attribute [instance] DirectedLocalHomApproximation.instIsLocalRingSStage
attribute [instance] DirectedLocalHomApproximation.stageMap_isLocalHom
attribute [instance] DirectedLocalHomApproximation.targetMap_isLocalHom
attribute [instance] DirectedLocalHomApproximation.instDirectedSystemTarget

namespace DirectedLocalHomApproximation

variable {f : R →+* S} (A : DirectedLocalHomApproximation f)

/-- View a source-facing local approximation through the neutral ReasLib owner.  The conversion
preserves every stage, transition map, comparison equivalence, and colimit compatibility datum. -/
@[stacks 00QT "legacy directed approximation bridge"]
def toApproximation : Ring.DirectLimit.Algebra.Approximation.Hom f where
  index := A.Λ
  preorder := A.instPreorder
  indexNonempty := A.instNonempty
  directedOrder := A.instDirectedOrder
  source := A.RStage
  target := A.SStage
  sourceCommRing := A.instCommRingRStage
  targetCommRing := A.instCommRingSStage
  sourceMap := A.map
  targetMap := A.targetMap
  sourceDirectedSystem := A.instDirectedSystemRStage
  targetDirectedSystem := A.instDirectedSystemTarget
  map := A.stageMap
  map_comm := fun h ↦ A.comm h
  sourceColimit := A.colimitIso
  targetColimit := A.targetColimit
  colimit_comm := A.colimit_comm

/-- The canonical map from a target stage of the source-facing approximation to the limit ring. -/
@[stacks 00QT "legacy directed approximation bridge"]
noncomputable abbrev targetStageToLimitHom (i : A.Λ) : A.SStage i →+* S :=
  Ring.DirectLimit.Algebra.Approximation.Hom.targetToLimit A.toApproximation i

/-- The tensor-product source of the canonical base-change map from stage `i` to stage `j`. -/
@[stacks 00QT "legacy approximation base-change source"]
abbrev targetStageBaseChange {i j : A.Λ} (h : i ≤ j) : Type _ :=
  Ring.DirectLimit.Algebra.Approximation.Hom.baseChange A.toApproximation h

/-- The canonical base-change map `Sᵢ ⊗[Rᵢ] Rⱼ → Sⱼ` attached to a transition `i ≤ j`. -/
@[stacks 00QT "legacy approximation base-change map"]
noncomputable abbrev stageBaseChangeMap {i j : A.Λ} (h : i ≤ j) :
    A.targetStageBaseChange h →+* A.SStage j :=
  Ring.DirectLimit.Algebra.Approximation.Hom.baseChangeMap A.toApproximation h

end DirectedLocalHomApproximation

#check @DirectedLocalHomApproximation.toApproximation
#check @DirectedLocalHomApproximation.targetStageToLimitHom
#check @DirectedLocalHomApproximation.targetStageBaseChange
#check @DirectedLocalHomApproximation.stageBaseChangeMap
#print axioms DirectedLocalHomApproximation.toApproximation

section

variable [IsLocalRing R] [IsLocalRing S]

/-- Lemma 10.127.9: a local homomorphism `f : R →+* S` of local rings admits a directed
approximation by local homomorphisms `R_λ → S_λ` of local rings such that each `R_λ` is
essentially of finite type over `ℤ`, each `S_λ` is essentially of finite type over `R_λ`, and the
induced map on direct limits identifies with `f`. -/
@[stacks 00QT]
theorem exists_directedLocalHomApproximation (f : R →+* S) [IsLocalHom f] :
    Nonempty (DirectedLocalHomApproximation.{u, v, max u v} f) := sorry

end
