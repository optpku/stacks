/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc

/-!
# Stability of standard fpqc covers

Standard fpqc covers of affine schemes are stable under singleton
isomorphisms, dependent composition, and pullback.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry.StandardFpqcCover

/-- The singleton family associated to an isomorphism onto an affine scheme,
as a standard fpqc cover. -/
noncomputable def singletonOfIsIso {T T' : Scheme.{u}} [IsAffine T]
    (f : T' ⟶ T) [IsIso f] : StandardFpqcCover T where
    isAffineTarget := inferInstance
    n := 1
    U := fun _ ↦ T'
    map := fun _ ↦ f
    isAffine := fun _ ↦ IsAffine.of_isIso f
    flat := fun _ ↦ MorphismProperty.of_isIso @Flat f
    cover := fun t ↦
      ⟨0, inv f t, by simp [← Scheme.Hom.comp_apply]⟩

/-- Each component of the singleton standard fpqc cover is the original
isomorphism. -/
theorem singletonOfIsIso_toOverFamily_obj {T T' : Scheme.{u}} [IsAffine T]
    (f : T' ⟶ T) [IsIso f] (j : Fin 1) :
    (singletonOfIsIso f).toOverFamily.obj j = Over.mk f := sorry

/-- Dependent composition of standard fpqc covers, canonically reindexed by a
finite ordinal. -/
noncomputable def comp {T : Scheme.{u}} (cover : StandardFpqcCover T)
    (refinement : ∀ i : Fin cover.n, StandardFpqcCover (cover.U i)) :
    StandardFpqcCover T :=
  let e : Fin (∑ i : Fin cover.n, (refinement i).n) ≃
      Sigma fun i : Fin cover.n ↦ Fin (refinement i).n :=
    finSigmaFinEquiv.symm
  let E :=
    (cover.toFlatCover.bind fun i ↦ (refinement i).toFlatCover).reindex e
  { isAffineTarget := cover.isAffineTarget
    n := ∑ i, (refinement i).n
    U := E.X
    map := E.f
    isAffine := fun k ↦
      (refinement (e k).1).isAffine (e k).2
    flat := Scheme.Cover.map_prop E
    cover := Scheme.Cover.exists_eq E }

/-- A component of a dependent composite is the corresponding refinement map
followed by the original chart map. -/
theorem comp_toOverFamily_obj {T : Scheme.{u}} (cover : StandardFpqcCover T)
    (refinement : ∀ i : Fin cover.n, StandardFpqcCover (cover.U i))
    (ij : Sigma fun i : Fin cover.n ↦ Fin (refinement i).n) :
    (comp cover refinement).toOverFamily.obj (finSigmaFinEquiv ij) =
      Over.mk ((refinement ij.1).map ij.2 ≫ cover.map ij.1) := sorry

/-- Pulling a standard fpqc cover back to an affine scheme gives a standard
fpqc cover with the same finite index type. -/
noncomputable def pullback {T T' : Scheme.{u}} [IsAffine T']
    (cover : StandardFpqcCover T) (f : T' ⟶ T) : StandardFpqcCover T' :=
  let E := cover.toFlatCover.pullback₁ f
  { isAffineTarget := inferInstance
    n := cover.n
    U := E.X
    map := E.f
    isAffine := fun i ↦
      @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine T' (cover.U i) T f (cover.map i)
        inferInstance (cover.isAffine i) cover.isAffineTarget
    flat := Scheme.Cover.map_prop E
    cover := Scheme.Cover.exists_eq E }

/-- A component of a pulled-back standard fpqc cover is the first projection
from the corresponding scheme pullback. -/
theorem pullback_toOverFamily_obj {T T' : Scheme.{u}} [IsAffine T']
    (cover : StandardFpqcCover T) (f : T' ⟶ T) (i : Fin cover.n) :
    (pullback cover f).toOverFamily.obj i =
      Over.mk (Limits.pullback.fst f (cover.map i)) := sorry

end AlgebraicGeometry.StandardFpqcCover
