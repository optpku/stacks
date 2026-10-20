/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubset.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Restriction
public import ReasLib.CategoryTheory.Functor.Algebraic.Instances
public import ReasLib.Topology.Sheaves.OpenCover.Gluing

/-!
# Descent data for sheaves of modules on an open family

This module specializes the neutral `C`-valued open-family formalism to sheaves of modules over a
ring sheaf.  It owns the module-linear overlap cocycle, realization predicate, and the canonical
`ModuleSheafOpenCover.Gluing` category.  Covering hypotheses occur only in descent constructions,
not in the local compatibility datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens
open SheafOfModules.OpenSubset.Restriction

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

namespace ModuleSheafOpenCover

variable (𝒪 : TopCat.Sheaf RingCat X)

/-- The overlap comparison from the first local module to the second on a triple intersection. -/
abbrev moduleTripleOverlapHom12
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (toTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (toTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) :=
  ((firstViaLeftIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((overlapToTripleLeft 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i j)).hom ≫
    ((secondViaLeftIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf j))

/-- The overlap comparison from the second local module to the third on a triple intersection. -/
abbrev moduleTripleOverlapHom23
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (toTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (toTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((secondViaCenterIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((overlapToTripleCenter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((thirdViaCenterIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

/-- The overlap comparison from the first local module to the third on a triple intersection. -/
abbrev moduleTripleOverlapHom13
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (toTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (toTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((firstViaOuterIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((overlapToTripleOuter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i k)).hom ≫
    ((thirdViaOuterIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

/-- The intrinsic cocycle condition for pairwise overlap isomorphisms of sheaves of modules:
on each triple overlap, the comparison from the first chart to the third is the composite through
the second chart. -/
def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  ∀ i j k : ι,
    moduleTripleOverlapHom12 𝒪 localSheaf overlapIso i j k ≫
        moduleTripleOverlapHom23 𝒪 localSheaf overlapIso i j k =
      moduleTripleOverlapHom13 𝒪 localSheaf overlapIso i j k

/-- An intrinsic module cocycle induces the cocycle of the underlying additive sheaves. -/
theorem CocycleCondition.toAdditive
    {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}
    {localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i)}
    {overlapIso : ∀ i j : ι,
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j)}
    (cocycle : CocycleCondition 𝒪 U localSheaf overlapIso) :
    TopCat.Sheaf.OpenCover.CocycleCondition (C := AddCommGrpCat.{w}) U
    (fun i ↦ (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))
    (fun i j ↦
      toAddCommGrpToPairLeftIso 𝒪 (U i) (U j) (localSheaf i) ≪≫
        ((SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).mapIso (overlapIso i j)) ≪≫
        (toAddCommGrpToPairRightIso 𝒪 (U i) (U j) (localSheaf j)).symm) := sorry

variable {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}

/-- The left comparison induced on an overlap by a family of local realization isomorphisms. -/
abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (functor (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (functor (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) :=
  ((toPairViaLeftIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((toPairLeft 𝒪 (U i) (U j)).mapIso (φ i)).hom

/-- The right comparison induced on an overlap by a family of local realization isomorphisms. -/
abbrev realizationRightHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (functor (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (functor (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j) :=
  ((toPairViaRightIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((toPairRight 𝒪 (U i) (U j)).mapIso (φ j)).hom

/-- A sheaf of `𝒪`-modules realizes a module gluing datum if its restrictions recover the given
local module sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in the categories of sheaves of `𝒪`-modules. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (ℱ : SheafOfModules 𝒪) : Prop :=
  ∃ φ : ∀ i : ι, (functor (U i) 𝒪).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end ModuleSheafOpenCover

namespace ModuleSheafOpenCover

variable {𝒪 : TopCat.Sheaf RingCat.{w} X}
variable {U : ι → Opens X}

/-- Module-linear descent data on an indexed family of open subsets.  The datum is local and does
not require that the family cover the ambient space. -/
structure Gluing (𝒪 : TopCat.Sheaf RingCat.{w} X) (U : ι → Opens X) where
  /-- The local module sheaf on each member of the family. -/
  localSheaf : ∀ i, SheafOfModules (𝒪 |_ U i)
  /-- The module-linear identification on each pairwise intersection. -/
  overlapIso : ∀ i j,
    (toPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (toPairRight 𝒪 (U i) (U j)).obj (localSheaf j)
  /-- The overlap identifications satisfy the module cocycle condition on triple intersections. -/
  cocycle : CocycleCondition 𝒪 U localSheaf overlapIso

namespace Gluing

/-- A morphism of module-sheaf gluing data is a compatible family of local module-sheaf
morphisms. -/
@[ext] structure Hom (A B : Gluing 𝒪 U) where
  /-- The module-sheaf morphism on each member of the open family. -/
  hom : ∀ i, A.localSheaf i ⟶ B.localSheaf i
  /-- The local morphisms commute with the prescribed overlap isomorphisms. -/
  comm : ∀ i j,
    (toPairLeft 𝒪 (U i) (U j)).map (hom i) ≫
        (B.overlapIso i j).hom =
      (A.overlapIso i j).hom ≫
        (toPairRight 𝒪 (U i) (U j)).map (hom j)

/-- Identity local morphisms commute with every module overlap isomorphism. -/
theorem id_comm (A : Gluing 𝒪 U) :
    ∀ i j,
      (toPairLeft 𝒪 (U i) (U j)).map
          (𝟙 (A.localSheaf i)) ≫
          (A.overlapIso i j).hom =
        (A.overlapIso i j).hom ≫
          (toPairRight 𝒪 (U i) (U j)).map
            (𝟙 (A.localSheaf j)) := sorry

/-- The identity morphism of module-sheaf gluing data. -/
def id (A : Gluing 𝒪 U) : Hom A A where
  hom i := 𝟙 (A.localSheaf i)
  comm := id_comm A

/-- Morphisms of module-sheaf gluing data are determined by their local components. -/
@[ext] theorem hom_ext {A B : Gluing 𝒪 U} {f g : Hom A B}
    (h : ∀ i, f.hom i = g.hom i) : f = g := sorry

/-- Componentwise composites of compatible module-sheaf morphisms remain compatible on
overlaps. -/
theorem comp_comm {A B D : Gluing 𝒪 U} (f : Hom A B) (g : Hom B D) :
    ∀ i j,
      (toPairLeft 𝒪 (U i) (U j)).map
          (f.hom i ≫ g.hom i) ≫
          (D.overlapIso i j).hom =
        (A.overlapIso i j).hom ≫
          (toPairRight 𝒪 (U i) (U j)).map
            (f.hom j ≫ g.hom j) := sorry

/-- Composition of morphisms of module-sheaf gluing data. -/
def comp {A B D : Gluing 𝒪 U} (f : Hom A B) (g : Hom B D) : Hom A D where
  hom i := f.hom i ≫ g.hom i
  comm := comp_comm f g

/-- Left identity for componentwise composition of module-sheaf gluing morphisms. -/
theorem id_comp {A B : Gluing 𝒪 U} (f : Hom A B) :
    comp (id A) f = f := sorry

/-- Right identity for componentwise composition of module-sheaf gluing morphisms. -/
theorem comp_id {A B : Gluing 𝒪 U} (f : Hom A B) :
    comp f (id B) = f := sorry

/-- Associativity of componentwise composition of module-sheaf gluing morphisms. -/
theorem assoc {A B D E : Gluing 𝒪 U}
    (f : Hom A B) (g : Hom B D) (h : Hom D E) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- Module-sheaf gluing data form a category under compatible local morphisms. -/
instance : Category (Gluing 𝒪 U) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

/-- A global module sheaf realizes gluing data when its restrictions recover the local module
sheaves and prescribed overlap maps. -/
abbrev Realizes (data : Gluing 𝒪 U) (ℱ : SheafOfModules 𝒪) : Prop :=
  ModuleSheafOpenCover.Realizes U data.localSheaf data.overlapIso ℱ

/-- Forget module structure in a module-sheaf gluing datum, yielding its additive-sheaf gluing
datum. -/
noncomputable def toAdditive (data : Gluing 𝒪 U) :
    TopCat.Sheaf.OpenCover.Gluing (C := AddCommGrpCat.{w}) U where
  localSheaf i := (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (data.localSheaf i)
  overlapIso i j :=
    toAddCommGrpToPairLeftIso 𝒪 (U i) (U j) (data.localSheaf i) ≪≫
      ((SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).mapIso (data.overlapIso i j)) ≪≫
      (toAddCommGrpToPairRightIso 𝒪 (U i) (U j) (data.localSheaf j)).symm
  cocycle := CocycleCondition.toAdditive data.cocycle

/-- The canonical module-linear overlap isomorphism obtained by restricting one global module
sheaf through two members of an open family. -/
noncomputable def overlapIsoOfSheaf (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) (i j : ι) (ℱ : SheafOfModules 𝒪) :
    (toPairLeft 𝒪 (U i) (U j)).obj
        ((functor (U i) 𝒪).obj ℱ) ≅
      (toPairRight 𝒪 (U i) (U j)).obj
        ((functor (U j) 𝒪).obj ℱ) :=
  ((toPairViaLeftIso 𝒪 (U i) (U j)).app ℱ).symm ≪≫
    (toPairViaRightIso 𝒪 (U i) (U j)).app ℱ

/-- The canonical module overlap isomorphisms of a global module sheaf satisfy the
triple-overlap cocycle condition. -/
theorem overlapIsoOfSheaf_cocycle (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) (ℱ : SheafOfModules 𝒪) :
    CocycleCondition 𝒪 U
      (fun i ↦ (functor (U i) 𝒪).obj ℱ)
      (fun i j ↦ overlapIsoOfSheaf 𝒪 U i j ℱ) := sorry

/-- The module gluing datum obtained by restricting a global module sheaf to an arbitrary open
family. -/
noncomputable def ofSheaf (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) (ℱ : SheafOfModules 𝒪) : Gluing 𝒪 U where
  localSheaf i := (functor (U i) 𝒪).obj ℱ
  overlapIso i j := overlapIsoOfSheaf 𝒪 U i j ℱ
  cocycle := overlapIsoOfSheaf_cocycle 𝒪 U ℱ

/-- The module gluing datum obtained by restriction is realized by the original global module
sheaf. -/
theorem ofSheaf_realizes (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) (ℱ : SheafOfModules 𝒪) :
    (ofSheaf 𝒪 U ℱ).Realizes ℱ := sorry

/-- Restriction of a global module-sheaf morphism is compatible with the canonical module
overlap isomorphisms. -/
theorem ofSheafMap_comm (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) {ℱ 𝒢 : SheafOfModules 𝒪} (η : ℱ ⟶ 𝒢) :
    ∀ i j,
      (toPairLeft 𝒪 (U i) (U j)).map
          ((functor (U i) 𝒪).map η) ≫
          (overlapIsoOfSheaf 𝒪 U i j 𝒢).hom =
        (overlapIsoOfSheaf 𝒪 U i j ℱ).hom ≫
          (toPairRight 𝒪 (U i) (U j)).map
            ((functor (U j) 𝒪).map η) := sorry

/-- A global module-sheaf morphism restricts to a morphism of module gluing data. -/
def ofSheafMap (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) {ℱ 𝒢 : SheafOfModules 𝒪} (η : ℱ ⟶ 𝒢) :
    Hom (ofSheaf 𝒪 U ℱ) (ofSheaf 𝒪 U 𝒢) where
  hom i := (functor (U i) 𝒪).map η
  comm := ofSheafMap_comm 𝒪 U η

/-- Restriction of the identity module-sheaf morphism is the identity gluing morphism. -/
theorem ofSheafMap_id (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) (ℱ : SheafOfModules 𝒪) :
    ofSheafMap 𝒪 U (𝟙 ℱ) = 𝟙 (ofSheaf 𝒪 U ℱ) := sorry

/-- Restriction of a composite is the composite of the restricted module gluing morphisms. -/
theorem ofSheafMap_comp (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) {ℱ 𝒢 ℋ : SheafOfModules 𝒪} (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    ofSheafMap 𝒪 U (η ≫ θ) =
      comp (ofSheafMap 𝒪 U η) (ofSheafMap 𝒪 U θ) := sorry

/-- Restriction from global module sheaves to module gluing data on an arbitrary open family. -/
noncomputable def ofSheafFunctor (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (U : ι → Opens X) : SheafOfModules 𝒪 ⥤ Gluing 𝒪 U where
  obj := ofSheaf 𝒪 U
  map := ofSheafMap 𝒪 U
  map_id := ofSheafMap_id 𝒪 U
  map_comp := ofSheafMap_comp 𝒪 U

/-- Every module-linear gluing datum on an open cover is realized by a sheaf of modules over
the ambient, possibly noncommutative ring sheaf. -/
theorem existsRealizingSheaf
    (data : Gluing 𝒪 U) (hU : IsOpenCover U) :
    ∃ sheaf : SheafOfModules 𝒪, data.Realizes sheaf := sorry

/-- Restriction of module sheaves to an open cover is essentially surjective onto module-linear
gluing data. -/
theorem ofSheafFunctor_essSurj
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (U : ι → Opens X) (hU : IsOpenCover U) :
    (ofSheafFunctor 𝒪 U).EssSurj := sorry

/-- Restriction to an open cover is an equivalence between sheaves of modules over a possibly
noncommutative ring sheaf and module-linear gluing data. -/
theorem ofSheafFunctor_isEquivalence
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (U : ι → Opens X) (hU : IsOpenCover U) :
    Functor.IsEquivalence (ofSheafFunctor 𝒪 U) := sorry

end Gluing

end ModuleSheafOpenCover

end
