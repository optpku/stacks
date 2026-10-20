/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.PrecoverageSite
public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig
public import ReasLib.CategoryTheory.Sites.Simplicial.SliceAugmentation
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Spaces-étale total site of a simplicial algebraic space

Objects of `SpacesEtale U` are algebraic spaces étale over some stage `U.obj n`.
A morphism is a commutative square: a simplex operator together with a map of
algebraic spaces over the corresponding structure map of `U`. Coverings are the
identity-degree étale covers.
-/

set_option backward.privateInPublic true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

/-- An object of the spaces-étale site of a simplicial algebraic space `U`: an
algebraic space étale over some stage `U.obj n`. -/
structure SpacesEtale.Obj {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) where
  /-- The simplicial degree `n` such that the object lives over `U.obj n`. -/
  index : SimplexCategoryᵒᵖ
  /-- An algebraic space étale over `U.obj index`. -/
  obj : spacesEtaleSite (U.obj index)

namespace SpacesEtale

variable {S : Scheme.{u}} {U : SimplicialObject (AlgebraicSpace S)}

/-- A morphism `Y ⟶ Z` in `Obj U` is a commutative square: a simplex
operator `φ : Z.index.unop ⟶ Y.index.unop` and a map of algebraic spaces
`Y.obj.left ⟶ Z.obj.left` over `U.map φ.op`. -/
structure Hom (Y Z : Obj U) where
  /-- The underlying simplex operator `φ : Z.index.unop ⟶ Y.index.unop`. -/
  simplex : Z.index.unop ⟶ Y.index.unop
  /-- The map of algebraic spaces `Y.obj.left ⟶ Z.obj.left`. -/
  hom : Y.obj.left ⟶ Z.obj.left
  /-- The square commutes: `hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op`. -/
  w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op

/-- The object of `Obj U` given by an étale algebraic space over `U.obj n`. -/
def ofStage (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) : Obj U where
  index := n
  obj := V

/-- The simplicial degree of `ofStage n V` is `n`. -/
theorem ofStage_index (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) :
    (ofStage n V).index = n :=
  rfl

/-- The underlying étale object of `ofStage n V` is `V`. -/
theorem ofStage_obj (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) :
    (ofStage n V).obj = V :=
  rfl

/-- Build a morphism of `Obj U` from a commutative square. -/
def homMk {Y Z : Obj U} (simplex : Z.index.unop ⟶ Y.index.unop)
    (hom : Y.obj.left ⟶ Z.obj.left)
    (w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op) : Hom Y Z where
  simplex := simplex
  hom := hom
  w := w

/-- The simplex operator of `homMk simplex hom w` is `simplex`. -/
theorem homMk_simplex {Y Z : Obj U} (simplex : Z.index.unop ⟶ Y.index.unop)
    (hom : Y.obj.left ⟶ Z.obj.left)
    (w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op) :
    (homMk simplex hom w).simplex = simplex :=
  rfl

/-- The underlying map of `homMk simplex hom w` is `hom`. -/
theorem homMk_hom {Y Z : Obj U} (simplex : Z.index.unop ⟶ Y.index.unop)
    (hom : Y.obj.left ⟶ Z.obj.left)
    (w : hom ≫ Z.obj.hom = Y.obj.hom ≫ U.map simplex.op) :
    (homMk simplex hom w).hom = hom :=
  rfl

/-- The identity simplex operator satisfies the commutativity condition. -/
theorem Hom.id_w (Y : Obj U) :
    𝟙 Y.obj.left ≫ Y.obj.hom = Y.obj.hom ≫ U.map (𝟙 Y.index.unop).op :=
  sorry

/-- The identity morphism of an object of `Obj U`. -/
def Hom.id (Y : Obj U) : Hom Y Y :=
  homMk (𝟙 Y.index.unop) (𝟙 Y.obj.left) (Hom.id_w Y)

/-- Composite simplex operators satisfy the commutativity condition. -/
theorem Hom.comp_w {Y Z W : Obj U} (f : Hom Y Z) (g : Hom Z W) :
    (f.hom ≫ g.hom) ≫ W.obj.hom =
      Y.obj.hom ≫ U.map (g.simplex ≫ f.simplex).op :=
  sorry

/-- Composition of morphisms of `Obj U` composes simplex operators and
underlying maps. -/
def Hom.comp {Y Z W : Obj U} (f : Hom Y Z) (g : Hom Z W) : Hom Y W :=
  homMk (g.simplex ≫ f.simplex) (f.hom ≫ g.hom) (Hom.comp_w f g)

/-- Left identity for morphisms of `Obj U`. -/
theorem Hom.id_comp {Y Z : Obj U} (f : Hom Y Z) :
    Hom.comp (Hom.id Y) f = f :=
  sorry

/-- Right identity for morphisms of `Obj U`. -/
theorem Hom.comp_id {Y Z : Obj U} (f : Hom Y Z) :
    Hom.comp f (Hom.id Z) = f :=
  sorry

/-- Associativity for morphisms of `Obj U`. -/
theorem Hom.assoc {Y Z W V : Obj U} (f : Hom Y Z) (g : Hom Z W) (h : Hom W V) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) :=
  sorry

/-- The category of algebraic spaces étale over the stages of `U`. -/
@[reducible]
def categoryData : Category.{u + 1} (Obj U) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end SpacesEtale

/-- The bundled category of algebraic spaces étale over the stages of a simplicial space. -/
def SpacesEtale {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) : Cat :=
  ⟨SpacesEtale.Obj U, SpacesEtale.categoryData⟩

namespace SpacesEtale

variable {S : Scheme.{u}} {U : SimplicialObject (AlgebraicSpace S)}

/-- Identity-simplex morphisms of `SpacesEtale U` satisfy the commutativity
condition. -/
theorem homOfStage_w {n : SimplexCategoryᵒᵖ} {V W : spacesEtaleSite (U.obj n)}
    (f : V ⟶ W) :
    f.left ≫ W.hom = V.hom ≫ U.map (𝟙 n.unop).op :=
  sorry

/-- The identity-simplex morphism of `SpacesEtale U` associated to a morphism of
étale objects over a fixed stage. -/
def homOfStage {n : SimplexCategoryᵒᵖ} {V W : spacesEtaleSite (U.obj n)} (f : V ⟶ W) :
    Hom (ofStage n V) (ofStage n W) :=
  homMk (𝟙 n.unop) f.left (homOfStage_w f)

/-- Stage inclusion preserves identities and composition. -/
private theorem includeStage_laws (n : SimplexCategoryᵒᵖ) :
    (∀ V : spacesEtaleSite (U.obj n), homOfStage (𝟙 V) = Hom.id (ofStage n V)) ∧
    (∀ {V W Z : spacesEtaleSite (U.obj n)} (f : V ⟶ W) (g : W ⟶ Z),
      homOfStage (f ≫ g) = Hom.comp (homOfStage f) (homOfStage g)) :=
  sorry

/-- The functor sending an étale object over `U.obj n` to the corresponding object
of `SpacesEtale U` on the identity simplex. -/
def includeStage (n : SimplexCategoryᵒᵖ) : spacesEtaleSite (U.obj n) ⥤ SpacesEtale U where
  obj V := ofStage n V
  map f := homOfStage f
  map_id := (includeStage_laws n).1
  map_comp := (includeStage_laws n).2

/-- `includeStage n` sends `V` to `ofStage n V`. -/
theorem includeStage_obj (n : SimplexCategoryᵒᵖ) (V : spacesEtaleSite (U.obj n)) :
    (includeStage n).obj V = ofStage n V :=
  rfl

/-- The adjunct of a commutative-square morphism as a map into the pullback along
the structure map of `U`. -/
def homEquivToPullback {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    Y.obj ⟶ (spacesEtalePullback (U.map f.simplex.op)).obj Z.obj :=
  MorphismProperty.Over.homMk
    (pullback.lift f.hom Y.obj.hom f.w)
    (pullback.lift_snd f.hom Y.obj.hom f.w) trivial

/-- Rebuilding a commutative-square morphism from a pullback-hom. -/
theorem homEquivFromPullback_w {Y Z : SpacesEtale U} (φ : Z.index.unop ⟶ Y.index.unop)
    (g : Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj) :
    (g.left ≫ pullback.fst Z.obj.hom (U.map φ.op)) ≫ Z.obj.hom =
      Y.obj.hom ≫ U.map φ.op :=
  sorry

/-- The commutative-square morphism associated to a simplex operator and a
pullback-hom. -/
def homEquivFromPullback {Y Z : SpacesEtale U} (φ : Z.index.unop ⟶ Y.index.unop)
    (g : Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj) : Y ⟶ Z :=
  homMk φ (g.left ≫ pullback.fst Z.obj.hom (U.map φ.op)) (homEquivFromPullback_w φ g)

/-- `homEquivFromPullback` recovers a commutative-square morphism from its adjunct. -/
theorem homEquiv_left_inv {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    homEquivFromPullback f.simplex (homEquivToPullback f) = f :=
  sorry

/-- `homEquivToPullback` recovers a pullback-hom from the rebuilt square. -/
theorem homEquiv_right_inv {Y Z : SpacesEtale U} (φ : Z.index.unop ⟶ Y.index.unop)
    (g : Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj) :
    homEquivToPullback (homEquivFromPullback φ g) = g :=
  sorry

/-- Morphisms `Y ⟶ Z` in `SpacesEtale U` are equivalently a simplex operator
`φ : Z.index.unop ⟶ Y.index.unop` together with a morphism
`Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj` over `U.obj Y.index`. -/
def homEquiv {Y Z : SpacesEtale U} :
    (Y ⟶ Z) ≃
      Σ φ : Z.index.unop ⟶ Y.index.unop,
        Y.obj ⟶ (spacesEtalePullback (U.map φ.op)).obj Z.obj where
  toFun f := ⟨f.simplex, homEquivToPullback f⟩
  invFun p := homEquivFromPullback p.1 p.2
  left_inv := homEquiv_left_inv
  right_inv := by
    intro ⟨φ, g⟩
    exact congrArg (fun g ↦ Sigma.mk φ g) (homEquiv_right_inv φ g)

/-- `homEquiv` unpacks a morphism as its simplex operator and adjunct pullback-hom. -/
theorem homEquiv_apply {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    homEquiv f = ⟨f.simplex, homEquivToPullback f⟩ :=
  rfl

/-- The simplex operator extracted by `homEquiv` is `f.simplex`. -/
theorem homEquiv_simplex {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    (homEquiv f).1 = f.simplex :=
  rfl

/-- Identity-degree covering families in `SpacesEtale U` are the images of stage
étale covering families under `includeStage`. -/
def ofStageArrows {Y : SpacesEtale U} {I : Type u} (V : I → spacesEtaleSite (U.obj Y.index))
    (p : ∀ i, V i ⟶ Y.obj) : Presieve Y :=
  Presieve.ofArrows (fun i ↦ ofStage Y.index (V i)) (fun i ↦ homOfStage (p i))

end SpacesEtale

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Identity-degree covering families in `SpacesEtale U`, transported from the
spaces-étale precoverage of the corresponding stage. -/
def spacesEtaleTotalPrecoverage : Precoverage (SpacesEtale U) where
  coverings Y :=
    { R |
        ∃ (I : Type u) (_ : Small.{u} I) (V : I → spacesEtaleSite (U.obj Y.index))
          (p : ∀ i, V i ⟶ Y.obj),
          R = SpacesEtale.ofStageArrows V p ∧
            Presieve.ofArrows V p ∈ spacesEtalePrecoverage (U.obj Y.index) Y.obj }

/-- A presieve covers in `spacesEtaleTotalPrecoverage U` iff it is the identity-degree
image of a spaces-étale covering of the underlying stage object. -/
theorem mem_spacesEtaleTotalPrecoverage_iff {Y : SpacesEtale U} {R : Presieve Y} :
    R ∈ spacesEtaleTotalPrecoverage U Y ↔
      ∃ (I : Type u) (_ : Small.{u} I) (V : I → spacesEtaleSite (U.obj Y.index))
        (p : ∀ i, V i ⟶ Y.obj),
        R = SpacesEtale.ofStageArrows V p ∧
          Presieve.ofArrows V p ∈ spacesEtalePrecoverage (U.obj Y.index) Y.obj :=
  sorry

/-- An identity-degree family covers in `spacesEtaleTotalPrecoverage U` iff the
underlying stage family covers. -/
theorem ofStageArrows_mem_spacesEtaleTotalPrecoverage_iff {Y : SpacesEtale U}
    {I : Type u} [Small.{u} I] (V : I → spacesEtaleSite (U.obj Y.index))
    (p : ∀ i, V i ⟶ Y.obj) :
    SpacesEtale.ofStageArrows V p ∈ spacesEtaleTotalPrecoverage U Y ↔
      Presieve.ofArrows V p ∈ spacesEtalePrecoverage (U.obj Y.index) Y.obj :=
  sorry

/-- Identity-degree étale covers of the stages of `U` satisfy the site axioms. -/
instance spacesEtaleTotalPrecoverage.instIsSite : (spacesEtaleTotalPrecoverage U).IsSite :=
  sorry

/-- The Grothendieck topology on `SpacesEtale U` generated by identity-degree stage
étale covers. -/
def spacesEtaleTotalTopology : GrothendieckTopology (SpacesEtale U) :=
  (spacesEtaleTotalPrecoverage U).toGrothendieck

/-- The total spaces-étale topology is generated by `spacesEtaleTotalPrecoverage U`. -/
theorem spacesEtaleTotalTopology_eq_toGrothendieck :
    spacesEtaleTotalTopology U = (spacesEtaleTotalPrecoverage U).toGrothendieck :=
  rfl

/-- The degree-zero pullback inclusion: pull back along
`a.app (op ⦋0⦌)` and include the resulting étale object at degree zero. -/
def augmentationFunctor {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    spacesEtaleSite X ⥤ SpacesEtale U :=
  spacesEtalePullback (a.app (op ⦋0⦌)) ⋙ SpacesEtale.includeStage (op ⦋0⦌)

/-- On objects, `augmentationFunctor a` is the degree-zero pullback along `a0`. -/
theorem augmentationFunctor_obj {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (V : spacesEtaleSite X) :
    (augmentationFunctor U a).obj V =
      SpacesEtale.ofStage (op ⦋0⦌) ((spacesEtalePullback (a.app (op ⦋0⦌))).obj V) :=
  rfl

/-- Base change along `a0` followed by identity-degree inclusion is continuous for
the spaces-étale topologies. -/
instance augmentationFunctor_isContinuous {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (augmentationFunctor U a).IsContinuous (spacesEtaleTopology X)
      (spacesEtaleTotalTopology U) :=
  sorry

/-- Fibre of `toSliceTotal` at an object of `SpacesEtale U`. -/
def toSliceTotalObj (Y : SpacesEtale U) : sliceTotalSite U :=
  ⟨Y.index, Over.mk Y.obj.hom⟩

/-- The Grothendieck fibre of a commutative-square morphism. -/
def toSliceTotalMap_fiber {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    ((sliceDiagram U).map f.simplex.op).toFunctor.obj (Over.mk Y.obj.hom) ⟶
      Over.mk Z.obj.hom :=
  Over.homMk f.hom f.w

/-- The morphism of Grothendieck objects associated to a commutative square. -/
def toSliceTotalMap {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    toSliceTotalObj U Y ⟶ toSliceTotalObj U Z where
  base := f.simplex.op
  fiber := toSliceTotalMap_fiber U f

/-- The total inclusion preserves identities and composition. -/
private theorem toSliceTotal_laws :
    (∀ Y : SpacesEtale U, toSliceTotalMap U (𝟙 Y) = 𝟙 (toSliceTotalObj U Y)) ∧
    (∀ {Y Z W : SpacesEtale U} (f : Y ⟶ Z) (g : Z ⟶ W),
      toSliceTotalMap U (f ≫ g) = toSliceTotalMap U f ≫ toSliceTotalMap U g) :=
  sorry

/-- The presenting functor of the top horizontal arrow: send an étale object over
`U.obj n` to the same morphism viewed in `(Spaces/U_n)_fppf`, as an object of
`(Spaces/U)_{fppf,total}`. -/
def toSliceTotal : SpacesEtale U ⥤ sliceTotalSite U where
  obj Y := toSliceTotalObj U Y
  map f := toSliceTotalMap U f
  map_id := (toSliceTotal_laws U).1
  map_comp := (toSliceTotal_laws U).2

/-- On objects, `toSliceTotal U` is the Grothendieck object with the same degree and
structure morphism. -/
theorem toSliceTotal_obj (Y : SpacesEtale U) :
    (toSliceTotal U).obj Y = ⟨Y.index, Over.mk Y.obj.hom⟩ :=
  rfl

/-- On morphisms, `toSliceTotal U` is the Grothendieck arrow with base `f.simplex.op`
and fibre `Over.homMk f.hom f.w`. -/
theorem toSliceTotal_map {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    (toSliceTotal U).map f = toSliceTotalMap U f :=
  rfl

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The two degree-zero presenting composites agree on objects: both send
`V` étale over `X` to the degree-zero object `V ×_X U_0` in the fppf total site. -/
theorem presentingCommSq_obj (V : spacesEtaleSite X) :
    (augmentationFunctor U a ⋙ toSliceTotal U).obj V =
      (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).obj V :=
  rfl

/-- The objectwise identification of presenting composites, as the identity on the
common degree-zero pullback object. -/
def presentingCommSq_app (V : spacesEtaleSite X) :
    (augmentationFunctor U a ⋙ toSliceTotal U).obj V ≅
      (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).obj V :=
  Iso.refl _

/-- Naturality of `presentingCommSq_app`. -/
theorem presentingCommSq_naturality {V W : spacesEtaleSite X} (f : V ⟶ W) :
    (augmentationFunctor U a ⋙ toSliceTotal U).map f ≫ (presentingCommSq_app U a W).hom =
      (presentingCommSq_app U a V).hom ≫
        (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).map f :=
  sorry

/-- The degree-zero presenting-functor square: pullback along `a0` then include into the fppf
total site agrees with forget-to-`Over X` then `sliceAugmentationPullback`. -/
def presentingCommSq :
    augmentationFunctor U a ⋙ toSliceTotal U ≅
      Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a :=
  NatIso.ofComponents (presentingCommSq_app U a) (fun f ↦ presentingCommSq_naturality U a f)

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
