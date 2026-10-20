/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Sheaves.OpenSubset.Restriction

/-!
# Gluing sheaves along an open family

This module owns descent data for sheaves on the members of an arbitrary indexed family of open
subsets.  The coefficient category is arbitrary.  A covering hypothesis is deliberately absent
from `Gluing`: it belongs to realization and descent-equivalence results, rather than to the
local compatibility datum itself.

The restriction functors below use `IsOpenEmbedding.sheafPullback`, the generic sheaf-restriction
construction.  This keeps the owner independent of the concrete pullback API for `Type`-valued
sheaves.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens
open TopCat.Opens.Subspace

noncomputable section

universe u v w z

namespace TopCat.Sheaf.OpenCover

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
variable {ι : Type w} {U : ι → Opens X}

/-- Restriction of `C`-valued sheaves from the ambient space to an open subset. -/
abbrev restrictToOpen (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (space U) :=
  U.isOpenEmbedding.sheafPullback C

/-- Restriction from the first member of a pair to its intersection with the second. -/
abbrev restrictToPairLeft (U V : Opens X) :
    TopCat.Sheaf C (space U) ⥤ TopCat.Sheaf C (space (U ⊓ V)) :=
  sheafPullback C (inf_le_left : U ⊓ V ≤ U)

/-- Restriction from the second member of a pair to its intersection with the first. -/
abbrev restrictToPairRight (U V : Opens X) :
    TopCat.Sheaf C (space V) ⥤ TopCat.Sheaf C (space (U ⊓ V)) :=
  sheafPullback C (inf_le_right : U ⊓ V ≤ V)

/-- Restriction from the first member of a triple to its triple intersection. -/
abbrev restrictToTripleFirst (U V W : Opens X) :
    TopCat.Sheaf C (space U) ⥤ TopCat.Sheaf C (space (U ⊓ V ⊓ W)) :=
  sheafPullback C
    ((inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V).trans (inf_le_left : U ⊓ V ≤ U))

/-- Restriction from the second member of a triple to its triple intersection. -/
abbrev restrictToTripleSecond (U V W : Opens X) :
    TopCat.Sheaf C (space V) ⥤ TopCat.Sheaf C (space (U ⊓ V ⊓ W)) :=
  sheafPullback C
    ((inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V).trans (inf_le_right : U ⊓ V ≤ V))

/-- Restriction from the third member of a triple to its triple intersection. -/
abbrev restrictToTripleThird (U V W : Opens X) :
    TopCat.Sheaf C (space W) ⥤ TopCat.Sheaf C (space (U ⊓ V ⊓ W)) :=
  sheafPullback C
    ((inf_le_inf inf_le_right le_rfl : U ⊓ V ⊓ W ≤ V ⊓ W).trans
      (inf_le_right : V ⊓ W ≤ W))

/-- Restriction from the left pairwise intersection to a triple intersection. -/
abbrev restrictOverlapToTripleLeft (U V W : Opens X) :
    TopCat.Sheaf C (space (U ⊓ V)) ⥤ TopCat.Sheaf C (space (U ⊓ V ⊓ W)) :=
  sheafPullback C (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V)

/-- Restriction from the central pairwise intersection to a triple intersection. -/
abbrev restrictOverlapToTripleCenter (U V W : Opens X) :
    TopCat.Sheaf C (space (V ⊓ W)) ⥤ TopCat.Sheaf C (space (U ⊓ V ⊓ W)) :=
  sheafPullback C (inf_le_inf inf_le_right le_rfl : U ⊓ V ⊓ W ≤ V ⊓ W)

/-- Restriction from the outer pairwise intersection to a triple intersection. -/
abbrev restrictOverlapToTripleOuter (U V W : Opens X) :
    TopCat.Sheaf C (space (U ⊓ W)) ⥤ TopCat.Sheaf C (space (U ⊓ V ⊓ W)) :=
  sheafPullback C (inf_le_inf inf_le_left le_rfl : U ⊓ V ⊓ W ≤ U ⊓ W)

/-- Direct restriction from the first member of a triple factors through the left pair. -/
noncomputable def restrictToTripleFirstViaLeftIso (U V W : Opens X) :
    (restrictToTripleFirst (C := C) U V W) ≅
      (restrictToPairLeft (C := C) U V) ⋙ restrictOverlapToTripleLeft (C := C) U V W :=
  (sheafPullbackCompIso (C := C)
    (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V)
    (inf_le_left : U ⊓ V ≤ U)).symm

/-- Direct restriction from the second member of a triple factors through the left pair. -/
noncomputable def restrictToTripleSecondViaLeftIso (U V W : Opens X) :
    (restrictToTripleSecond (C := C) U V W) ≅
      (restrictToPairRight (C := C) U V) ⋙ restrictOverlapToTripleLeft (C := C) U V W :=
  (sheafPullbackCompIso (C := C)
    (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V)
    (inf_le_right : U ⊓ V ≤ V)).symm

/-- Direct restriction from the second member of a triple factors through the central pair. -/
noncomputable def restrictToTripleSecondViaCenterIso (U V W : Opens X) :
    (restrictToTripleSecond (C := C) U V W) ≅
      (restrictToPairLeft (C := C) V W) ⋙ restrictOverlapToTripleCenter (C := C) U V W :=
  (sheafPullbackCompIso (C := C)
    (inf_le_inf inf_le_right le_rfl : U ⊓ V ⊓ W ≤ V ⊓ W)
    (inf_le_left : V ⊓ W ≤ V)).symm

/-- Direct restriction from the third member of a triple factors through the central pair. -/
noncomputable def restrictToTripleThirdViaCenterIso (U V W : Opens X) :
    (restrictToTripleThird (C := C) U V W) ≅
      (restrictToPairRight (C := C) V W) ⋙ restrictOverlapToTripleCenter (C := C) U V W :=
  (sheafPullbackCompIso (C := C)
    (inf_le_inf inf_le_right le_rfl : U ⊓ V ⊓ W ≤ V ⊓ W)
    (inf_le_right : V ⊓ W ≤ W)).symm

/-- Direct restriction from the first member of a triple factors through the outer pair. -/
noncomputable def restrictToTripleFirstViaOuterIso (U V W : Opens X) :
    (restrictToTripleFirst (C := C) U V W) ≅
      (restrictToPairLeft (C := C) U W) ⋙ restrictOverlapToTripleOuter (C := C) U V W :=
  (sheafPullbackCompIso (C := C)
    (inf_le_inf (inf_le_left : U ⊓ V ≤ U) le_rfl : U ⊓ V ⊓ W ≤ U ⊓ W)
    (inf_le_left : U ⊓ W ≤ U)).symm

/-- Direct restriction from the third member of a triple factors through the outer pair. -/
noncomputable def restrictToTripleThirdViaOuterIso (U V W : Opens X) :
    (restrictToTripleThird (C := C) U V W) ≅
      (restrictToPairRight (C := C) U W) ⋙ restrictOverlapToTripleOuter (C := C) U V W :=
  (sheafPullbackCompIso (C := C)
    (inf_le_inf (inf_le_left : U ⊓ V ≤ U) le_rfl : U ⊓ V ⊓ W ≤ U ⊓ W)
    (inf_le_right : U ⊓ W ≤ W)).symm

/-- Global restriction to a pairwise intersection factors through its left member. -/
noncomputable def globalRestrictionToPairViaLeftIso (U V : Opens X) :
    (restrictToOpen (C := C) (U ⊓ V)) ≅
      (restrictToOpen (C := C) U) ⋙ restrictToPairLeft (C := C) U V :=
  (sheafPullbackCompInclusionIso (C := C)
    (inf_le_left : U ⊓ V ≤ U)).symm

/-- Global restriction to a pairwise intersection factors through its right member. -/
noncomputable def globalRestrictionToPairViaRightIso (U V : Opens X) :
    (restrictToOpen (C := C) (U ⊓ V)) ≅
      (restrictToOpen (C := C) V) ⋙ restrictToPairRight (C := C) U V :=
  (sheafPullbackCompInclusionIso (C := C)
    (inf_le_right : U ⊓ V ≤ V)).symm

namespace Gluing

/-- A family of identifications between the restrictions of local sheaves to pairwise overlaps. -/
abbrev OverlapIso
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (space (U i))) :=
  ∀ i j,
    (restrictToPairLeft (C := C) (U i) (U j)).obj (localSheaf i) ≅
      (restrictToPairRight (C := C) (U i) (U j)).obj (localSheaf j)

end Gluing

/-- The transition induced on a triple overlap by the left pairwise overlap isomorphism. -/
abbrev tripleOverlapHom12
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (space (U i)))
    (overlapIso : Gluing.OverlapIso (C := C) localSheaf)
    (i j k : ι) :
    (restrictToTripleFirst (C := C) (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (restrictToTripleSecond (C := C) (U i) (U j) (U k)).obj (localSheaf j) :=
  ((restrictToTripleFirstViaLeftIso (C := C) (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((restrictOverlapToTripleLeft (C := C) (U i) (U j) (U k)).mapIso
      (overlapIso i j)).hom ≫
    ((restrictToTripleSecondViaLeftIso (C := C) (U i) (U j) (U k)).inv.app (localSheaf j))

/-- The transition induced on a triple overlap by the central pairwise overlap isomorphism. -/
abbrev tripleOverlapHom23
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (space (U i)))
    (overlapIso : Gluing.OverlapIso (C := C) localSheaf)
    (i j k : ι) :
    (restrictToTripleSecond (C := C) (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (restrictToTripleThird (C := C) (U i) (U j) (U k)).obj (localSheaf k) :=
  ((restrictToTripleSecondViaCenterIso (C := C) (U i) (U j) (U k)).hom.app
      (localSheaf j)) ≫
    ((restrictOverlapToTripleCenter (C := C) (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((restrictToTripleThirdViaCenterIso (C := C) (U i) (U j) (U k)).inv.app
      (localSheaf k))

/-- The direct transition induced on a triple overlap by the outer pairwise isomorphism. -/
abbrev tripleOverlapHom13
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (space (U i)))
    (overlapIso : Gluing.OverlapIso (C := C) localSheaf)
    (i j k : ι) :
    (restrictToTripleFirst (C := C) (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (restrictToTripleThird (C := C) (U i) (U j) (U k)).obj (localSheaf k) :=
  ((restrictToTripleFirstViaOuterIso (C := C) (U i) (U j) (U k)).hom.app
      (localSheaf i)) ≫
    ((restrictOverlapToTripleOuter (C := C) (U i) (U j) (U k)).mapIso
      (overlapIso i k)).hom ≫
    ((restrictToTripleThirdViaOuterIso (C := C) (U i) (U j) (U k)).inv.app
      (localSheaf k))

/-- The cocycle condition for pairwise overlap isomorphisms on an open family. -/
def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (space (U i)))
    (overlapIso : Gluing.OverlapIso (C := C) localSheaf) : Prop :=
  ∀ i j k : ι,
    tripleOverlapHom12 (C := C) localSheaf overlapIso i j k ≫
        tripleOverlapHom23 (C := C) localSheaf overlapIso i j k =
      tripleOverlapHom13 (C := C) localSheaf overlapIso i j k

/-- `C`-valued descent data on an arbitrary indexed family of open subsets. -/
structure Gluing (U : ι → Opens X) where
  /-- The local sheaf on each member of the family. -/
  localSheaf : ∀ i, TopCat.Sheaf C (space (U i))
  /-- The identification of the restrictions to each pairwise intersection. -/
  overlapIso : Gluing.OverlapIso (C := C) localSheaf
  /-- The pairwise identifications satisfy the triple-overlap cocycle. -/
  cocycle : CocycleCondition (C := C) U localSheaf overlapIso

namespace Gluing

/-- A morphism of gluing data is a compatible family of local sheaf morphisms. -/
@[ext] structure Hom (A B : Gluing (C := C) U) where
  /-- The local component of the morphism. -/
  hom : ∀ i, A.localSheaf i ⟶ B.localSheaf i
  /-- Compatibility with pairwise overlap identifications. -/
  comm : ∀ i j,
    (restrictToPairLeft (C := C) (U i) (U j)).map (hom i) ≫
        (B.overlapIso i j).hom =
      (A.overlapIso i j).hom ≫
        (restrictToPairRight (C := C) (U i) (U j)).map (hom j)

attribute [reassoc] Hom.comm

/-- Identity components commute with every overlap isomorphism. -/
theorem id_comm (A : Gluing (C := C) U) :
    ∀ i j,
      (restrictToPairLeft (C := C) (U i) (U j)).map (𝟙 (A.localSheaf i)) ≫
          (A.overlapIso i j).hom =
        (A.overlapIso i j).hom ≫
          (restrictToPairRight (C := C) (U i) (U j)).map (𝟙 (A.localSheaf j)) := sorry

/-- The identity morphism of gluing data. -/
def id (A : Gluing (C := C) U) : Hom A A where
  hom i := 𝟙 (A.localSheaf i)
  comm := id_comm A

/-- Morphisms of gluing data are determined by their local components. -/
@[ext] theorem hom_ext {A B : Gluing (C := C) U} {f g : Hom A B}
    (h : ∀ i, f.hom i = g.hom i) : f = g := sorry

/-- Componentwise composition preserves overlap compatibility. -/
theorem comp_comm {A B D : Gluing (C := C) U} (f : Hom A B) (g : Hom B D) :
    ∀ i j,
      (restrictToPairLeft (C := C) (U i) (U j)).map (f.hom i ≫ g.hom i) ≫
          (D.overlapIso i j).hom =
        (A.overlapIso i j).hom ≫
          (restrictToPairRight (C := C) (U i) (U j)).map (f.hom j ≫ g.hom j) := sorry

/-- Composition of morphisms of gluing data. -/
def comp {A B D : Gluing (C := C) U} (f : Hom A B) (g : Hom B D) : Hom A D where
  hom i := f.hom i ≫ g.hom i
  comm := comp_comm f g

/-- Left identity for gluing morphisms. -/
theorem id_comp {A B : Gluing (C := C) U} (f : Hom A B) :
    comp (id A) f = f := sorry

/-- Right identity for gluing morphisms. -/
theorem comp_id {A B : Gluing (C := C) U} (f : Hom A B) :
    comp f (id B) = f := sorry

/-- Associativity of gluing morphism composition. -/
theorem assoc {A B D E : Gluing (C := C) U}
    (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- Gluing data on an open family form a category. -/
instance : Category (Gluing (C := C) U) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

/-- The local component of the identity morphism of gluing data is an identity morphism. -/
@[simp]
theorem id_hom (A : Gluing (C := C) U) (i : ι) :
    (𝟙 A : A ⟶ A).hom i = 𝟙 _ := sorry

/-- The local component of a composite of gluing morphisms is the composite of the local
components. -/
@[simp, reassoc]
theorem comp_hom {A B D : Gluing (C := C) U} (f : A ⟶ B) (g : B ⟶ D) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i := sorry

/-- Apply a coefficient functor which preserves sheaves on every open subspace to a gluing datum.
This is the coefficient-change owner for open-cover descent data; special cases such as forgetting
algebraic structure should use this construction. -/
noncomputable def map
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    (data : Gluing (C := C) U) : Gluing (C := D) U where
  localSheaf i :=
    (sheafCompose (Opens.grothendieckTopology (space (U i))) F).obj
      (data.localSheaf i)
  overlapIso i j :=
    (sheafCompose (Opens.grothendieckTopology (space (U i ⊓ U j))) F).mapIso
      (data.overlapIso i j)
  cocycle := sorry

/-- Coefficient change commutes with selecting the local sheaf on a member of the open family. -/
@[simp]
theorem map_localSheaf
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    (data : Gluing (C := C) U) (i : ι) :
    (map F data).localSheaf i =
      (sheafCompose (Opens.grothendieckTopology (space (U i))) F).obj
        (data.localSheaf i) := sorry

/-- Coefficient change applies `sheafCompose` to each prescribed overlap isomorphism. -/
@[simp]
theorem map_overlapIso
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    (data : Gluing (C := C) U) (i j : ι) :
    (map F data).overlapIso i j =
      (sheafCompose (Opens.grothendieckTopology (space (U i ⊓ U j))) F).mapIso
        (data.overlapIso i j) := sorry

/-- Apply coefficient change to a morphism of gluing data. -/
noncomputable def mapHom
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    {A B : Gluing (C := C) U} (f : A ⟶ B) :
    map F A ⟶ map F B where
  hom i :=
    (sheafCompose (Opens.grothendieckTopology (space (U i))) F).map (f.hom i)
  comm := sorry

/-- Coefficient change applies `sheafCompose` componentwise to a gluing morphism. -/
@[simp]
theorem mapHom_hom
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    {A B : Gluing (C := C) U} (f : A ⟶ B) (i : ι) :
    (mapHom F f).hom i =
      (sheafCompose (Opens.grothendieckTopology (space (U i))) F).map (f.hom i) := sorry

/-- The functor on gluing-data categories induced by a coefficient functor which preserves sheaves
on every open subspace. -/
noncomputable def mapFunctor
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F] :
    Gluing (C := C) U ⥤ Gluing (C := D) U where
  obj := map F
  map := mapHom F
  map_id := sorry
  map_comp := sorry

/-- The object part of `mapFunctor` is coefficient change of gluing data. -/
@[simp]
theorem mapFunctor_obj
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    (data : Gluing (C := C) U) :
    (mapFunctor F).obj data = map F data := sorry

/-- The morphism part of `mapFunctor` is componentwise coefficient change. -/
@[simp]
theorem mapFunctor_map
    {D : Type z} [Category.{u} D] (F : C ⥤ D)
    [∀ V : Opens X,
      (Opens.grothendieckTopology (space V)).HasSheafCompose F]
    {A B : Gluing (C := C) U} (f : A ⟶ B) :
    (mapFunctor F).map f = mapHom F f := sorry

end Gluing

namespace Gluing

/-- The overlap comparison from a proposed realization of a gluing datum through its left
chart. -/
abbrev realizationLeftHom (data : Gluing (C := C) U)
    (F : TopCat.Sheaf C X)
    (phi : ∀ i : ι, (restrictToOpen (C := C) (U i)).obj F ≅ data.localSheaf i)
    (i j : ι) :
    (restrictToOpen (C := C) (U i ⊓ U j)).obj F ⟶
      (restrictToPairLeft (C := C) (U i) (U j)).obj (data.localSheaf i) :=
  ((globalRestrictionToPairViaLeftIso (C := C) (U i) (U j)).hom.app F) ≫
    ((restrictToPairLeft (C := C) (U i) (U j)).mapIso (phi i)).hom

/-- The overlap comparison from a proposed realization of a gluing datum through its right
chart. -/
abbrev realizationRightHom (data : Gluing (C := C) U)
    (F : TopCat.Sheaf C X)
    (phi : ∀ i : ι, (restrictToOpen (C := C) (U i)).obj F ≅ data.localSheaf i)
    (i j : ι) :
    (restrictToOpen (C := C) (U i ⊓ U j)).obj F ⟶
      (restrictToPairRight (C := C) (U i) (U j)).obj (data.localSheaf j) :=
  ((globalRestrictionToPairViaRightIso (C := C) (U i) (U j)).hom.app F) ≫
    ((restrictToPairRight (C := C) (U i) (U j)).mapIso (phi j)).hom

/-- A global sheaf realizes a gluing datum when its local restriction isomorphisms recover the
prescribed overlap maps. -/
def Realizes (data : Gluing (C := C) U) (F : TopCat.Sheaf C X) : Prop :=
  ∃ phi : ∀ i : ι, (restrictToOpen (C := C) (U i)).obj F ≅ data.localSheaf i,
    ∀ i j : ι,
      data.realizationLeftHom F phi i j ≫ (data.overlapIso i j).hom =
        data.realizationRightHom F phi i j

/-- The canonical overlap isomorphism produced by restricting a global sheaf. -/
noncomputable def overlapIsoOfSheaf (U : ι → Opens X) (i j : ι)
    (F : TopCat.Sheaf C X) :
    (restrictToPairLeft (C := C) (U i) (U j)).obj
        ((restrictToOpen (C := C) (U i)).obj F) ≅
      (restrictToPairRight (C := C) (U i) (U j)).obj
        ((restrictToOpen (C := C) (U j)).obj F) :=
  ((globalRestrictionToPairViaLeftIso (C := C) (U i) (U j)).app F).symm ≪≫
    (globalRestrictionToPairViaRightIso (C := C) (U i) (U j)).app F

/-- The canonical overlap isomorphisms of a global sheaf satisfy the cocycle condition. -/
theorem overlapIsoOfSheaf_cocycle (U : ι → Opens X) (F : TopCat.Sheaf C X) :
    CocycleCondition (C := C) U
      (fun i ↦ (restrictToOpen (C := C) (U i)).obj F)
      (fun i j ↦ overlapIsoOfSheaf U i j F) := sorry

/-- The gluing datum obtained by restricting a global sheaf to an arbitrary open family. -/
noncomputable def ofSheaf (U : ι → Opens X) (F : TopCat.Sheaf C X) : Gluing (C := C) U where
  localSheaf i := (restrictToOpen (C := C) (U i)).obj F
  overlapIso i j := overlapIsoOfSheaf U i j F
  cocycle := overlapIsoOfSheaf_cocycle U F

/-- The canonical gluing datum obtained by restriction is realized by the sheaf from which it
was constructed. -/
theorem ofSheaf_realizes (U : ι → Opens X) (F : TopCat.Sheaf C X) :
    (ofSheaf U F).Realizes F := sorry

/-- Restriction of a global morphism is compatible with canonical overlap isomorphisms. -/
@[reassoc]
theorem ofSheafMap_comm (U : ι → Opens X) {F G : TopCat.Sheaf C X} (eta : F ⟶ G) :
    ∀ i j,
      (restrictToPairLeft (C := C) (U i) (U j)).map
          ((restrictToOpen (C := C) (U i)).map eta) ≫
          (overlapIsoOfSheaf U i j G).hom =
        (overlapIsoOfSheaf U i j F).hom ≫
          (restrictToPairRight (C := C) (U i) (U j)).map
            ((restrictToOpen (C := C) (U j)).map eta) := sorry

/-- A global sheaf morphism restricts to a gluing morphism. -/
def ofSheafMap (U : ι → Opens X) {F G : TopCat.Sheaf C X} (eta : F ⟶ G) :
    Hom (ofSheaf U F) (ofSheaf U G) where
  hom i := (restrictToOpen (C := C) (U i)).map eta
  comm := ofSheafMap_comm U eta

/-- The local component of the gluing morphism induced by a global sheaf morphism is its
restriction to that chart. -/
@[simp]
theorem ofSheafMap_hom (U : ι → Opens X) {F G : TopCat.Sheaf C X} (eta : F ⟶ G) (i : ι) :
    (ofSheafMap U eta).hom i = (restrictToOpen (C := C) (U i)).map eta := sorry

/-- Restriction preserves identity morphisms. -/
theorem ofSheafMap_id (U : ι → Opens X) (F : TopCat.Sheaf C X) :
    ofSheafMap U (𝟙 F) = 𝟙 (ofSheaf U F) := sorry

/-- Restriction preserves compositions of morphisms. -/
theorem ofSheafMap_comp (U : ι → Opens X)
    {F G H : TopCat.Sheaf C X} (eta : F ⟶ G) (theta : G ⟶ H) :
    ofSheafMap U (eta ≫ theta) = comp (ofSheafMap U eta) (ofSheafMap U theta) := sorry

/-- Restriction from global sheaves to gluing data on an arbitrary open family. -/
noncomputable def ofSheafFunctor (U : ι → Opens X) :
    TopCat.Sheaf C X ⥤ Gluing (C := C) U where
  obj := ofSheaf U
  map := ofSheafMap U
  map_id := ofSheafMap_id U
  map_comp := ofSheafMap_comp U

/-- The chart opens of an open family: an open `V` of the subspace `U i` is sent to its image in
the ambient space. -/
abbrev chartOpen (U : ι → Opens X) (p : Σ i, Opens (space (U i))) : Opens X :=
  (U p.1).isOpenEmbedding.functor.obj p.2

/-- For an open cover, the chart opens of all members form a basis of the ambient topology: an
ambient open `W` around `x ∈ U i` contains the chart open `W ∩ U i`. -/
theorem isBasis_range_chartOpen (U : ι → Opens X) (hU : IsOpenCover U) :
    Opens.IsBasis (Set.range (chartOpen U)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  have hxU : x ∈ iSup U := by
    rw [show iSup U = ⊤ from hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  refine ⟨chartOpen U ⟨i, (Opens.map (U i).inclusion').obj W⟩, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [chartOpen, TopologicalSpace.Opens.functor_map_eq_inf]
    exact ⟨hx, hi⟩
  · rw [chartOpen, TopologicalSpace.Opens.functor_map_eq_inf]
    exact inf_le_left

/-- The local components of a morphism of canonical gluing data, read on the chart-open basis of
the ambient space. The component at the chart open of `V ⊆ U i` is the component at `V` of the
local morphism on `U i`. -/
noncomputable def chartBasisHom (U : ι → Opens X) {F G : TopCat.Sheaf C X}
    (f : ofSheaf U F ⟶ ofSheaf U G) :
    (inducedFunctor (chartOpen U)).op ⋙ F.presheaf ⟶
      (inducedFunctor (chartOpen U)).op ⋙ G.presheaf where
  app p := (f.hom p.unop.1).hom.app (Opposite.op p.unop.2)
  naturality := sorry

/-- Glue a morphism of canonical gluing data over an open cover to a global sheaf morphism
(Stacks 04TN). The gluing is mathlib's extension of morphisms from the chart-open basis,
applied to the local components of the gluing morphism. -/
noncomputable def glueHom (U : ι → Opens X) (hU : IsOpenCover U) {F G : TopCat.Sheaf C X}
    (f : ofSheaf U F ⟶ ofSheaf U G) : F ⟶ G :=
  Sheaf.homEquiv.symm
    (TopCat.Sheaf.restrictHomEquivHom F.presheaf G (isBasis_range_chartOpen U hU)
      (chartBasisHom U f))

/-- On the chart open of `V ⊆ U i`, the glued morphism has the prescribed local component. -/
theorem glueHom_app_chartOpen (U : ι → Opens X) (hU : IsOpenCover U)
    {F G : TopCat.Sheaf C X} (f : ofSheaf U F ⟶ ofSheaf U G)
    (i : ι) (V : Opens (space (U i))) :
    (glueHom U hU f).hom.app (Opposite.op (chartOpen U ⟨i, V⟩)) =
      (f.hom i).hom.app (Opposite.op V) :=
  TopCat.Sheaf.extend_hom_app F.presheaf G (isBasis_range_chartOpen U hU)
    (chartBasisHom U f) ⟨i, V⟩

/-- Restriction to an open cover is fully faithful for sheaves valued in any coefficient category
(Stacks 04TN, 00AN). The preimage is the glued morphism `glueHom`. Essential surjectivity requires
additional descent hypotheses and is supplied separately by the algebraic basis construction. -/
noncomputable def ofSheafFunctorFullyFaithful (U : ι → Opens X) (hU : IsOpenCover U) :
    (ofSheafFunctor (C := C) U).FullyFaithful where
  preimage f := glueHom U hU f
  map_preimage := sorry
  preimage_map := sorry

/-- The preimage of the fully faithful restriction functor is the glued morphism. -/
@[simp]
theorem ofSheafFunctorFullyFaithful_preimage (U : ι → Opens X) (hU : IsOpenCover U)
    {F G : TopCat.Sheaf C X} (f : ofSheaf U F ⟶ ofSheaf U G) :
    (ofSheafFunctorFullyFaithful (C := C) U hU).preimage f = glueHom U hU f := rfl

/-- Restriction to an open cover is fully faithful. -/
theorem ofSheafFunctor_fullyFaithful (U : ι → Opens X) (hU : IsOpenCover U) :
    Nonempty (ofSheafFunctor (C := C) U).FullyFaithful :=
  ⟨ofSheafFunctorFullyFaithful U hU⟩

/-- The canonical equivalence between global sheaf morphisms and morphisms of their restriction
gluing data over an open cover. -/
noncomputable def ofSheafFunctorHomEquiv
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X) :
    (F ⟶ G) ≃ (ofSheaf U F ⟶ ofSheaf U G) :=
  (ofSheafFunctorFullyFaithful (C := C) U hU).homEquiv

/-- The forward map of `ofSheafFunctorHomEquiv` is restriction of a global sheaf morphism. -/
@[simp]
theorem ofSheafFunctorHomEquiv_apply
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X) (f : F ⟶ G) :
    ofSheafFunctorHomEquiv U hU F G f = ofSheafMap U f := sorry

/-- The global morphism reconstructed from a morphism of canonical gluing data restricts to its
specified local component on every member of the open cover. -/
@[simp]
theorem ofSheafFunctorHomEquiv_symm_apply_hom
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X)
    (f : ofSheaf U F ⟶ ofSheaf U G) (i : ι) :
    (restrictToOpen (C := C) (U i)).map
        ((ofSheafFunctorHomEquiv U hU F G).symm f) = f.hom i := sorry

end Gluing

end TopCat.Sheaf.OpenCover

end
