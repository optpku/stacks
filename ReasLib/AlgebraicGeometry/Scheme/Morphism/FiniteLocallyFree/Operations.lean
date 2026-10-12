/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType

/-!
# Operations on finite locally free scheme morphisms

This file contains characterization, composition, base-change, and
constant-rank decomposition APIs for finite locally free scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A morphism is finite locally free exactly when it is finite, flat, and locally of finite
presentation. -/
theorem finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := sorry

/-- Construct a finite locally free morphism from finiteness, flatness, and local finite
presentation. -/
theorem isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
    (hfinite : IsFinite f) (hflat : Flat f) (hlfp : LocallyOfFinitePresentation f) :
    IsFiniteLocallyFree f := sorry

/-- A finite locally free morphism is finite. -/
theorem IsFiniteLocallyFree.isFinite
    (h : IsFiniteLocallyFree f) :
    IsFinite f := sorry

/-- A finite locally free morphism is flat. -/
theorem IsFiniteLocallyFree.flat
    (h : IsFiniteLocallyFree f) :
    Flat f := sorry

/-- A finite locally free morphism is locally of finite presentation. -/
theorem IsFiniteLocallyFree.locallyOfFinitePresentation
    (h : IsFiniteLocallyFree f) :
    LocallyOfFinitePresentation f := sorry

/-- Finite local freeness supplies finiteness to typeclass search. -/
instance instIsFiniteOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    IsFinite f := sorry

/-- Finite local freeness supplies flatness to typeclass search. -/
instance instFlatOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    Flat f := sorry

/-- Finite local freeness supplies local finite presentation to typeclass search. -/
instance instLocallyOfFinitePresentationOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    LocallyOfFinitePresentation f := sorry

/-- Finite local freeness is equivalent to the affine-local finite-free ring-map condition. -/
theorem finiteLocallyFree_iff_locallyOfType_ringHomFiniteFree :
    IsFiniteLocallyFree f ↔ LocallyOfType RingHom.FiniteFree f := sorry

/-- A finite locally free morphism satisfies the affine-local finite-free ring-map condition. -/
theorem IsFiniteLocallyFree.locallyOfType_ringHomFiniteFree
    (h : IsFiniteLocallyFree f) :
    LocallyOfType RingHom.FiniteFree f := sorry

/-- Finite local freeness supplies the affine-local finite-free ring-map condition to typeclass
search. -/
instance instLocallyOfTypeRingHomFiniteFreeOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    LocallyOfType RingHom.FiniteFree f := sorry

/-- Over a locally Noetherian base, finite local freeness is equivalent to finiteness and
flatness. -/
theorem finiteLocallyFree_iff_isFinite_and_flat [IsLocallyNoetherian S] :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f := sorry

end

/-- Finite locally free scheme morphisms form a morphism property stable under composition. -/
instance finiteLocallyFree_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsFiniteLocallyFree := sorry

namespace IsFiniteLocallyFree

/-- The composite of two finite locally free morphisms is finite locally free. -/
theorem comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFiniteLocallyFree f) (hg : IsFiniteLocallyFree g) :
    IsFiniteLocallyFree (f ≫ g) := sorry

/-- A finite locally free morphism remains finite locally free after arbitrary base change. -/
theorem pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : IsFiniteLocallyFree f) :
    IsFiniteLocallyFree (pullback.snd f g) := sorry

end IsFiniteLocallyFree

/-- Typeclass form of closure of finite locally free morphisms under composition. -/
instance instIsFiniteLocallyFreeComp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsFiniteLocallyFree f] [IsFiniteLocallyFree g] :
    IsFiniteLocallyFree (f ≫ g) := sorry

/-- Finite locally free scheme morphisms form a morphism property stable under base change. -/
instance finiteLocallyFree_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsFiniteLocallyFree := sorry

/-- Typeclass form of closure of finite locally free morphisms under base change. -/
instance instIsFiniteLocallyFreePullbackSndOfIsFiniteLocallyFree
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsFiniteLocallyFree f] :
    IsFiniteLocallyFree (pullback.snd f g) := sorry

section

variable {X S : Scheme.{u}}

/-- A finite locally free morphism has a clopen decomposition of the base on which its rank is
constant. -/
theorem exists_clopen_degree_decomposition_of_isFiniteLocallyFree
    (f : X ⟶ S) [IsFiniteLocallyFree f] :
    ∃ Sdegree : ℕ → S.Opens,
      iSup Sdegree = ⊤ ∧
        Pairwise (fun d e ↦ Disjoint (Sdegree d : Set S) (Sdegree e : Set S)) ∧
        (∀ d, IsClopen (Sdegree d : Set S)) ∧
        ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ (Sdegree d)) d := sorry

end

end AlgebraicGeometry
