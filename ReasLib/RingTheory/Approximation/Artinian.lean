/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

/-!
# Approximation by Artinian local subalgebras

The main result gives a directed-subalgebra presentation rather than a
chapter-specific diagram.  This makes its flatness, maximal-ideal, and
essential-finiteness properties directly available to later approximation
arguments.
-/

open IsLocalRing

universe u v w

namespace Algebra.ArtinianApproximation

/-- One Artinian local approximation stage inside a local `k`-algebra. Its
canonical algebraic properties are instance fields, so they remain available
to typeclass search after a stage is selected from a directed system. -/
@[stacks 07FG "Artinian local approximation stage"]
structure Stage (k : Type u) [CommRing k] (A : Type v) [CommRing A]
    [IsLocalRing A] [Algebra k A] where
  /-- The approximation subalgebra. -/
  carrier : Subalgebra k A
  /-- The approximation stage is Artinian. -/
  [isArtinianRing : IsArtinianRing carrier]
  /-- The approximation stage is local. -/
  [isLocalRing : IsLocalRing carrier]
  /-- Its inclusion into the ambient algebra is flat. -/
  [flat : Module.Flat carrier A]
  /-- Its maximal ideal extends to the maximal ideal of the ambient algebra. -/
  mapsMaximalIdeal : RingHom.MapsMaximalIdeal (algebraMap carrier A)
  /-- The approximation stage is essentially of finite type over `k`. -/
  [essFiniteType : Algebra.EssFiniteType k carrier]

attribute [instance] Stage.isArtinianRing Stage.isLocalRing Stage.flat
  Stage.essFiniteType

namespace Stage

/-- Build an Artinian approximation stage from a subalgebra carrying the
canonical stage properties. -/
@[stacks 07FG "Artinian approximation stage constructor"]
def of
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (B : Subalgebra k A) [IsArtinianRing B] [IsLocalRing B]
    [Module.Flat B A] (hmax : RingHom.MapsMaximalIdeal (algebraMap B A))
    [Algebra.EssFiniteType k B] :
    Stage k A :=
  { carrier := B
    mapsMaximalIdeal := hmax }

/-- The carrier of a stage built by `Stage.of` is the supplied subalgebra. -/
@[simp]
theorem carrier_of
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (B : Subalgebra k A) [IsArtinianRing B] [IsLocalRing B]
    [Module.Flat B A] (hmax : RingHom.MapsMaximalIdeal (algebraMap B A))
    [Algebra.EssFiniteType k B] :
    (of B hmax).carrier = B := rfl

namespace carrier

/-- An Artinian approximation stage has the characteristic of its base
field. -/
@[stacks 07FG "characteristic of an Artinian approximation stage"]
instance charP
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] {p : ℕ} [CharP k p] (S : Stage k A) :
    CharP S.carrier p :=
  charP_of_injective_algebraMap (algebraMap k S.carrier).injective p

end carrier

/-- The source-semantic properties carried by an Artinian approximation
stage. -/
@[stacks 07FG "Artinian approximation stage specification"]
theorem spec
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : Stage k A) :
    IsArtinianRing S.carrier ∧
      IsLocalRing S.carrier ∧
      Module.Flat S.carrier A ∧
      RingHom.MapsMaximalIdeal (algebraMap S.carrier A) ∧
      Algebra.EssFiniteType k S.carrier :=
  ⟨inferInstance, inferInstance, inferInstance, S.mapsMaximalIdeal, inferInstance⟩

namespace algebraMap

/-- The inclusion of an Artinian approximation stage into the ambient local
algebra is local. -/
instance isLocal
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : Stage k A) :
    IsLocalHom (algebraMap S.carrier A) :=
  ((local_hom_TFAE (algebraMap S.carrier A)).out 2 0).mp S.mapsMaximalIdeal.le

end algebraMap

end Stage

/-- A nonempty directed system of Artinian approximation stages whose union
is the ambient algebra. -/
@[stacks 07FG "directed Artinian approximation system"]
structure System (k : Type u) [CommRing k] (A : Type v) [CommRing A]
    [IsLocalRing A] [Algebra k A] where
  /-- The index type of the approximation system. -/
  ι : Type w
  /-- The approximation system has at least one stage. -/
  [nonemptyIndex : Nonempty ι]
  /-- The Artinian approximation stage at an index. -/
  stage : ι → Stage k A
  /-- Any two approximation stages are contained in a common later stage. -/
  directed : Directed (· ≤ ·) (fun i ↦ (stage i).carrier)
  /-- The approximation stages exhaust the ambient algebra. -/
  iSup_eq_top : iSup (fun i ↦ (stage i).carrier) = (⊤ : Subalgebra k A)

attribute [instance] System.nonemptyIndex

namespace System

/-- Build a directed Artinian approximation system from its stages,
directedness, and exhaustion property. -/
@[stacks 07FG "directed Artinian approximation system constructor"]
def of
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] {ι : Type w} [Nonempty ι] (stage : ι → Stage k A)
    (directed : Directed (· ≤ ·) (fun i ↦ (stage i).carrier))
    (iSup_eq_top : iSup (fun i ↦ (stage i).carrier) =
      (⊤ : Subalgebra k A)) :
    System.{u, v, w} k A :=
  { ι := ι
    stage := stage
    directed := directed
    iSup_eq_top := iSup_eq_top }

/-- The stages of a system built by `System.of` are the supplied stages. -/
@[simp]
theorem stage_of
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] {ι : Type w} [Nonempty ι] (stage : ι → Stage k A)
    (directed : Directed (· ≤ ·) (fun i ↦ (stage i).carrier))
    (iSup_eq_top : iSup (fun i ↦ (stage i).carrier) =
      (⊤ : Subalgebra k A)) (i : ι) :
    (of stage directed iSup_eq_top).stage i = stage i := rfl

/-- The canonical algebra map between two stages when the first stage is
contained in the second. -/
def transition
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) {i j : S.ι}
    (h : (S.stage i).carrier ≤ (S.stage j).carrier) :
    (S.stage i).carrier →ₐ[k] (S.stage j).carrier :=
  Subalgebra.inclusion h

/-- A transition map is the inclusion of its source stage into the ambient
algebra. -/
@[simp]
theorem coe_transition
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) {i j : S.ι}
    (h : (S.stage i).carrier ≤ (S.stage j).carrier)
    (x : (S.stage i).carrier) :
    ((S.transition h x : (S.stage j).carrier) : A) = x := rfl

/-- The transition from a stage to itself is the identity algebra map. -/
@[simp]
theorem transition_id
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) (i : S.ι) :
    S.transition (le_refl (S.stage i).carrier) =
      AlgHom.id k (S.stage i).carrier :=
  Subalgebra.inclusion_self

/-- Transition maps compose as inclusions of Artinian approximation
stages. -/
@[simp]
theorem transition_comp
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) {i j l : S.ι}
    (hij : (S.stage i).carrier ≤ (S.stage j).carrier)
    (hjl : (S.stage j).carrier ≤ (S.stage l).carrier) :
    (S.transition hjl).comp (S.transition hij) =
      S.transition (hij.trans hjl) :=
  AlgHom.ext fun _ ↦ Subtype.ext rfl

/-- The nonemptiness, directedness, and exhaustion properties of an Artinian
approximation system. -/
@[stacks 07FG "Artinian approximation system specification"]
theorem spec
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) :
    Nonempty S.ι ∧
      Directed (· ≤ ·) (fun i ↦ (S.stage i).carrier) ∧
      iSup (fun i ↦ (S.stage i).carrier) = (⊤ : Subalgebra k A) :=
  ⟨S.nonemptyIndex, S.directed, S.iSup_eq_top⟩

/-- Every element of the ambient algebra belongs to some stage of an
Artinian approximation system. -/
@[stacks 07FG "element captured by an Artinian approximation system"]
theorem exists_mem
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) (x : A) :
    ∃ i, x ∈ (S.stage i).carrier := by
  have hx : x ∈ ((⨆ i, (S.stage i).carrier : Subalgebra k A) : Set A) := by
    rw [S.iSup_eq_top]
    exact Algebra.mem_top
  rw [Subalgebra.coe_iSup_of_directed S.directed] at hx
  exact Set.mem_iUnion.mp hx

/-- Every finite subset of the ambient algebra is contained in one stage of
an Artinian approximation system. -/
@[stacks 07FG "finite subset captured by an Artinian approximation system"]
theorem exists_contains_finset
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [IsLocalRing A]
    [Algebra k A] (S : System k A) (E : Finset A) :
    ∃ i, ∀ x ∈ E, x ∈ (S.stage i).carrier := by
  have hdir : Directed (· ⊆ ·) (fun i ↦ ((S.stage i).carrier : Set A)) :=
    S.directed
  exact hdir.exists_mem_subset_of_finset_subset_biUnion
    (fun x _ ↦ Set.mem_iUnion.mpr (S.exists_mem x))

/-- Lemma 16.11.1: an Artinian local algebra in positive characteristic whose
residue-field cotangent homology is finite-dimensional admits a directed
Artinian approximation system. -/
@[stacks 07FG]
theorem nonempty
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsArtinianRing A]
    [IsLocalRing A] [Algebra k A] {p : ℕ} [Fact p.Prime] [CharP k p]
    [FiniteDimensional (ResidueField A) (Algebra.H1Cotangent k (ResidueField A))] :
    Nonempty (System.{u, v, max u v} k A) := sorry

end System

end Algebra.ArtinianApproximation
