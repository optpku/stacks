/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily

/-!
# Operations on finite affine families

This leaf supplies reindexing, composition, singleton, finite-coproduct
singleton, and affine base-change constructors for `AffineFamilyOver`.
Topology-specific closure theorems live with the corresponding cover condition.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

noncomputable section

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- Reindex a finite affine family over an arbitrary finite type by `Fin`. -/
def ofFintype (I : Type v) [Fintype I] (U : I → Scheme.{u})
    (map : (i : I) → U i ⟶ T) (isAffine : ∀ i, IsAffine (U i)) :
    AffineFamilyOver T where
  n := Fintype.card I
  U := fun j ↦ U ((Fintype.equivFin I).symm j)
  map := fun j ↦ map ((Fintype.equivFin I).symm j)
  isAffine := fun j ↦ isAffine ((Fintype.equivFin I).symm j)

/-- The `j`-th chart map of `ofFintype` is the original map at the
corresponding finite index. -/
@[simp]
theorem ofFintype_map (I : Type v) [Fintype I] (U : I → Scheme.{u})
    (map : (i : I) → U i ⟶ T) (isAffine : ∀ i, IsAffine (U i))
    (j : Fin (Fintype.card I)) :
    (ofFintype I U map isAffine).map j = map ((Fintype.equivFin I).symm j) := sorry

/-- The sigma-indexed composite of a finite affine family with finite affine
families over its charts. -/
def comp (family : AffineFamilyOver T)
    (refining : (i : Fin family.n) → AffineFamilyOver (family.U i)) :
    AffineFamilyOver T :=
  ofFintype
    (Sigma fun i : Fin family.n ↦ Fin (refining i).n)
    (fun p ↦ (refining p.1).U p.2)
    (fun p ↦ (refining p.1).map p.2 ≫ family.map p.1)
    (fun p ↦ (refining p.1).isAffine p.2)

/-- The map of a component in a composite affine family is the corresponding
refining chart followed by the original chart map. -/
@[simp]
theorem comp_map (family : AffineFamilyOver T)
    (refining : (i : Fin family.n) → AffineFamilyOver (family.U i))
    (k : Fin (family.comp refining).n) :
    (family.comp refining).map k =
      let p := (Fintype.equivFin (Sigma fun i : Fin family.n ↦ Fin (refining i).n)).symm k
      (refining p.1).map p.2 ≫ family.map p.1 := sorry

/-- The singleton affine family associated to one map with affine source. -/
def singleton {U V : Scheme.{u}} (map : V ⟶ U) (hV : IsAffine V) :
    AffineFamilyOver U where
  n := 1
  U := fun _ ↦ V
  map := fun _ ↦ map
  isAffine := fun _ ↦ hV

/-- The unique map of a singleton affine family is its defining map. -/
@[simp]
theorem singleton_map {U V : Scheme.{u}} (map : V ⟶ U)
    (hV : IsAffine V) (j : Fin 1) :
    (singleton map hV).map j = map := sorry

/-- The finite coproduct of the sources of an affine family is affine. -/
theorem coproduct_isAffine (family : AffineFamilyOver T) :
    IsAffine (∐ family.U) := sorry

/-- The singleton affine family whose source is the coproduct of the sources
and whose map is induced by the maps of the original family. -/
def coproductSingleton (family : AffineFamilyOver T) : AffineFamilyOver T :=
  singleton (Sigma.desc family.map) (coproduct_isAffine family)

/-- The source of the unique member of `coproductSingleton` is the coproduct
of the sources of the original family. -/
@[simp]
theorem coproductSingleton_U (family : AffineFamilyOver T) (j : Fin 1) :
    (coproductSingleton family).U j = ∐ family.U := sorry

/-- The unique map of `coproductSingleton` is induced by the maps of the
original family. -/
@[simp]
theorem coproductSingleton_map (family : AffineFamilyOver T) (j : Fin 1) :
    (coproductSingleton family).map j = Sigma.desc family.map := sorry

variable {T' : Scheme.{u}}

/-- The source chart of an affine base change is affine when the new target is affine. -/
theorem pullback_isAffine (family : AffineFamilyOver T) (g : T' ⟶ T)
    [IsAffine T'] (j : Fin family.n) :
    IsAffine (pullback g (family.map j)) := sorry

/-- The affine base change of a finite affine family. -/
def pullback (family : AffineFamilyOver T) (g : T' ⟶ T) [IsAffine T'] :
    AffineFamilyOver T' where
  n := family.n
  U := fun j ↦ Limits.pullback g (family.map j)
  map := fun j ↦ Limits.pullback.fst g (family.map j)
  isAffine := fun j ↦ pullback_isAffine family g j

/-- The map of a chart in a pullback affine family is the first pullback projection. -/
@[simp]
theorem pullback_map (family : AffineFamilyOver T) (g : T' ⟶ T)
    [IsAffine T'] (j : Fin family.n) :
    (pullback family g).map j = Limits.pullback.fst g (family.map j) := sorry

/-- The coherence equation used by the canonical base-change witness. -/
theorem pullback_baseChange_map_eq (family : AffineFamilyOver T) (g : T' ⟶ T)
    [IsAffine T'] (j : Fin family.n) :
    (Iso.refl (Limits.pullback g (family.map j))).hom ≫ (pullback family g).map j =
      Limits.pullback.fst g (family.map j) := sorry

/-- The pullback affine family is canonically the componentwise base change of
the original family. -/
def pullback_isBaseChangeOf (family : AffineFamilyOver T) (g : T' ⟶ T)
    [IsAffine T'] :
    IsBaseChangeOf g family (pullback family g) where
  indexEquiv := Equiv.refl _
  componentIso := fun _ ↦ Iso.refl _
  map_eq := fun j ↦ pullback_baseChange_map_eq family g j

/-- The canonical pullback base-change witness is identity on chart indices. -/
@[simp]
theorem pullback_isBaseChangeOf_indexEquiv (family : AffineFamilyOver T)
    (g : T' ⟶ T) [IsAffine T'] (j : Fin family.n) :
    (pullback_isBaseChangeOf family g).indexEquiv j = j := sorry

/-- The canonical pullback base-change witness uses identity component isomorphisms. -/
@[simp]
theorem pullback_isBaseChangeOf_componentIso_hom (family : AffineFamilyOver T)
    (g : T' ⟶ T) [IsAffine T'] (j : Fin family.n) :
    ((pullback_isBaseChangeOf family g).componentIso j).hom = 𝟙 _ := sorry

/-- The canonical pullback base-change witness is compatible with chart maps. -/
theorem pullback_isBaseChangeOf_map_eq (family : AffineFamilyOver T)
    (g : T' ⟶ T) [IsAffine T'] (j : Fin family.n) :
    ((pullback_isBaseChangeOf family g).componentIso j).hom ≫
        (pullback family g).map ((pullback_isBaseChangeOf family g).indexEquiv j) =
      Limits.pullback.fst g (family.map j) := sorry

end AffineFamilyOver

end

end AlgebraicGeometry
