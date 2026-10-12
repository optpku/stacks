/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase

/-!
# Change-of-base equivalence for algebraic spaces

A morphism `g : S ⟶ S'` induces an equivalence between algebraic spaces over `S` and
objects of `Over (ofOver (Over.mk g))`, i.e. algebraic spaces over `S'` equipped with a
morphism to `S` over `S'`. The forward functor is `j_!` together with the canonical
structure morphism; the inverse is the Type `u` fiber of that structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The triangle identity for the structure morphism of `T`, viewed over `S'`. -/
theorem structureIndex_w {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    T.hom ≫ (Over.mk g).hom = ((Over.map g).obj T).hom := sorry

/-- The structure morphism of `T` over `S`, viewed as a morphism `j(T) ⟶ S` over `S'`. -/
def structureIndex {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    (Over.map g).obj T ⟶ Over.mk g :=
  Over.homMk T.hom (structureIndex_w g T)

/-- The underlying scheme morphism of `structureIndex g T` is `T.hom`. -/
@[simp]
theorem structureIndex_left {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    (structureIndex g T).left = T.hom := sorry

/-- Viewing the index of `structureIndex g T` back over `S` recovers `T`. -/
theorem structureIndex_mk {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    Over.mk (structureIndex g T).left = T := sorry

/-- The canonical structure morphism `j_! F ⟶ S` of algebraic spaces over `S'`, projecting
the coproduct index of `extendBasePresheaf`. -/
def extendBaseHom {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    extendBase g F ⟶ ofOver (Over.mk g) where
  app T' := ofHom fun σ ↦ σ.1
  naturality := fun _ _ _ ↦ sorry

/-- Evaluating `extendBaseHom g F` at `T'` returns the coproduct index. -/
theorem extendBaseHom_app {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T' : Over S'} (φ : T' ⟶ Over.mk g)
    (s : F.functorOfPoints.obj (op (Over.mk φ.left))) :
    (extendBaseHom g F).app (op T') ⟨φ, s⟩ = φ := sorry

/-- A morphism of algebraic spaces over `S` induces a morphism of their extensions to `S'`. -/
def extendBaseMap {S S' : Scheme.{u}} (g : S ⟶ S') {F G : AlgebraicSpace S} (f : F ⟶ G) :
    extendBase g F ⟶ extendBase g G :=
  extendBasePresheafMap g f

/-- Extension of scalars `j_!` as a functor on algebraic spaces. -/
def extendBaseFunctor {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S ⥤ AlgebraicSpace S' where
  obj F := extendBase g F
  map f := extendBaseMap g f
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The structure morphisms `extendBaseHom g F` are natural in `F`. -/
theorem extendBaseHom_naturality {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (extendBaseFunctor g).map f ≫ extendBaseHom g G = extendBaseHom g F := sorry

/-- The comparison functor sending `F` to the object `(j_! F, j_! F ⟶ S)` of the slice. -/
def extendBaseOver {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S ⥤ Over (ofOver (Over.mk g)) :=
  (extendBaseFunctor g).toOver (ofOver (Over.mk g)) (extendBaseHom g)
    (extendBaseHom_naturality g)

/-- On objects, `extendBaseOver g` is the slice object of `extendBaseHom g F`. -/
@[simp]
theorem extendBaseOver_obj {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    (extendBaseOver g).obj F = Over.mk (extendBaseHom g F) := sorry

/-- The underlying algebraic space of `(extendBaseOver g).obj F` is `extendBase g F`. -/
@[simp]
theorem extendBaseOver_obj_left {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    ((extendBaseOver g).obj F).left = extendBase g F := sorry

/-- The structure morphism of `(extendBaseOver g).obj F` is `extendBaseHom g F`. -/
@[simp]
theorem extendBaseOver_obj_hom {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    ((extendBaseOver g).obj F).hom = extendBaseHom g F := sorry

/-- Sections of `X` over `j(T)` lying over the structure map of `T`. -/
def restrictOverSection {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) (T : Over S) : Type u :=
  { s : X.left.functorOfPoints.obj (op ((Over.map g).obj T)) //
    X.hom.app (op ((Over.map g).obj T)) s = structureIndex g T }

/-- Restriction of a fiber section along a morphism of schemes over `S`. -/
theorem restrictOverSection_map_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T T' : Over S} (f : T' ⟶ T)
    (s : restrictOverSection X T) :
    X.hom.app (op ((Over.map g).obj T'))
        (X.left.functorOfPoints.map ((Over.map g).map f).op s.1) =
      structureIndex g T' := sorry

/-- The inverse functor of points: the Type `u` fiber of `X.hom` over `structureIndex`. -/
def restrictOverPresheaf {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := restrictOverSection X T.unop
  map {T T'} f := ofHom fun s ↦
    ⟨X.left.functorOfPoints.map ((Over.map g).map f.unop).op s.1,
      restrictOverSection_map_mem X f.unop s⟩
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The algebraic space over `S` associated to a pair `(F', F' ⟶ S)` over `S'`. -/
def restrictOver {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : AlgebraicSpace S :=
  ofFunctor (restrictOverPresheaf X) sorry sorry sorry

/-- The functor of points of `restrictOver X` is the fiber presheaf of `X.hom`. -/
@[simp]
theorem restrictOver_functorOfPoints {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    (restrictOver X).functorOfPoints = restrictOverPresheaf X := sorry

/-- A morphism of pairs over `S` induces a map of fiber sections. -/
theorem restrictOverMap_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y) {T : Over S}
    (s : restrictOverSection X T) :
    Y.hom.app (op ((Over.map g).obj T))
        (f.left.app (op ((Over.map g).obj T)) s.1) =
      structureIndex g T := sorry

/-- A morphism of pairs over `S'` induces a morphism of the associated spaces over `S`. -/
def restrictOverMap {S S' : Scheme.{u}} {g : S ⟶ S'}
    {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y) :
    restrictOver X ⟶ restrictOver Y where
  app T := ofHom fun s ↦
    ⟨f.left.app (op ((Over.map g).obj T.unop)) s.1, restrictOverMap_mem f s⟩
  naturality := fun _ _ _ ↦ sorry

/-- The inverse comparison functor, sending a pair `(F', F' ⟶ S)` to its fiber over `S`. -/
def restrictOverFunctor {S S' : Scheme.{u}} (g : S ⟶ S') :
    Over (ofOver (Over.mk g)) ⥤ AlgebraicSpace S where
  obj X := restrictOver X
  map f := restrictOverMap f
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The triangle identifying `j` of the index of `φ : T' ⟶ S` with `T'` itself. -/
theorem viewedIndexIso_w {S S' : Scheme.{u}} {g : S ⟶ S'} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) :
    (Iso.refl ((Over.map g).obj (Over.mk φ.left)).left).hom ≫ T'.hom =
      ((Over.map g).obj (Over.mk φ.left)).hom := sorry

/-- Viewing `T'` over `S` along `φ : T' ⟶ S` and then applying `j = Over.map g` recovers
`T'` up to the slice identification. -/
def viewedIndexIso {S S' : Scheme.{u}} {g : S ⟶ S'} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) :
    (Over.map g).obj (Over.mk φ.left) ≅ T' :=
  Over.isoMk (Iso.refl _) (viewedIndexIso_w φ)

/-- A section of `F` lies in the fiber of `extendBaseHom g F` over `structureIndex`. -/
theorem extendBaseUnitHom_app_mem {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) {T : Over S} (s : F.functorOfPoints.obj (op T)) :
    (extendBaseHom g F).app (op ((Over.map g).obj T))
        ⟨structureIndex g T,
          F.functorOfPoints.map (eqToHom (structureIndex_mk g T).symm).op s⟩ =
      structureIndex g T := sorry

/-- The component of the unit at an object of `Over S`. -/
def extendBaseUnitHom_app {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) {T : Over S} (s : F.functorOfPoints.obj (op T)) :
    restrictOverSection (Over.mk (extendBaseHom g F)) T :=
  ⟨⟨structureIndex g T,
      F.functorOfPoints.map (eqToHom (structureIndex_mk g T).symm).op s⟩,
    extendBaseUnitHom_app_mem g F s⟩

/-- The unit morphism `F ⟶ restrictOver (j_! F ⟶ S)`. -/
def extendBaseUnitHom {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    F ⟶ restrictOver (Over.mk (extendBaseHom g F)) where
  app T := ofHom fun s ↦ extendBaseUnitHom_app g F s
  naturality := fun _ _ _ ↦ sorry

/-- The index of a fiber of `extendBaseHom g F` over `structureIndex` recovers `T`. -/
theorem restrictOverSection_extendBase_mk {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S}
    (σ : restrictOverSection (Over.mk (extendBaseHom g F)) T) :
    Over.mk σ.1.1.left = T := sorry

/-- The inverse unit extracts the `F`-component of a fiber of `extendBaseHom`. -/
def extendBaseUnitInv_app {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) {T : Over S}
    (σ : restrictOverSection (Over.mk (extendBaseHom g F)) T) :
    F.functorOfPoints.obj (op T) :=
  F.functorOfPoints.map (eqToHom (restrictOverSection_extendBase_mk g σ).symm).op σ.1.2

/-- The inverse unit morphism `restrictOver (j_! F ⟶ S) ⟶ F`. -/
def extendBaseUnitInv {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    restrictOver (Over.mk (extendBaseHom g F)) ⟶ F where
  app T := ofHom fun σ ↦ extendBaseUnitInv_app g F σ
  naturality := fun _ _ _ ↦ sorry

/-- The unit isomorphism of the change-of-base equivalence, at an algebraic space over `S`. -/
def extendBaseUnitAppIso {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    F ≅ restrictOver ((extendBaseOver g).obj F) where
  hom := extendBaseUnitHom g F
  inv := extendBaseUnitInv g F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Naturality of the unit components. -/
theorem extendBaseUnitIso_naturality {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : AlgebraicSpace S} (f : F ⟶ G) :
    f ≫ (extendBaseUnitAppIso g G).hom =
      (extendBaseUnitAppIso g F).hom ≫
        (extendBaseOver g ⋙ restrictOverFunctor g).map f := sorry

/-- The unit isomorphism `𝟭 ≅ extendBaseOver g ⋙ restrictOverFunctor g`. -/
def extendBaseUnitIso {S S' : Scheme.{u}} (g : S ⟶ S') :
    𝟭 (AlgebraicSpace S) ≅ extendBaseOver g ⋙ restrictOverFunctor g :=
  NatIso.ofComponents (fun F ↦ extendBaseUnitAppIso g F)
    (extendBaseUnitIso_naturality g)

/-- Transporting a fiber section along `viewedIndexIso` yields a section of `X.left`. -/
def extendBaseCounitHom_app {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T' : Over S'}
    (σ : (extendBasePresheaf g (restrictOverPresheaf X)).obj (op T')) :
    X.left.functorOfPoints.obj (op T') :=
  X.left.functorOfPoints.map (viewedIndexIso σ.1).inv.op σ.2.1

/-- The forward counit map `j_! (restrictOver X) ⟶ X.left`. -/
def extendBaseCounitHom {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    extendBase g (restrictOver X) ⟶ X.left where
  app T' := ofHom fun σ ↦ extendBaseCounitHom_app X σ
  naturality := fun _ _ _ ↦ sorry

/-- A section of `X.left` over `T'` lies in the fiber over its structure map. -/
theorem extendBaseCounitInv_app_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T' : Over S'}
    (t : X.left.functorOfPoints.obj (op T')) :
    X.hom.app (op ((Over.map g).obj (Over.mk (X.hom.app (op T') t).left)))
        (X.left.functorOfPoints.map (viewedIndexIso (X.hom.app (op T') t)).hom.op t) =
      structureIndex g (Over.mk (X.hom.app (op T') t).left) := sorry

/-- The inverse counit packages a section of `X.left` as a coproduct fiber. -/
def extendBaseCounitInv_app {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T' : Over S'}
    (t : X.left.functorOfPoints.obj (op T')) :
    (extendBasePresheaf g (restrictOverPresheaf X)).obj (op T') :=
  ⟨X.hom.app (op T') t,
    ⟨X.left.functorOfPoints.map (viewedIndexIso (X.hom.app (op T') t)).hom.op t,
      extendBaseCounitInv_app_mem X t⟩⟩

/-- The inverse counit map `X.left ⟶ j_! (restrictOver X)`. -/
def extendBaseCounitInv {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    X.left ⟶ extendBase g (restrictOver X) where
  app T' := ofHom fun t ↦ extendBaseCounitInv_app X t
  naturality := fun _ _ _ ↦ sorry

/-- The underlying isomorphism of algebraic spaces in the counit. -/
def extendBaseCounitLeftIso {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    extendBase g (restrictOver X) ≅ X.left where
  hom := extendBaseCounitHom X
  inv := extendBaseCounitInv X
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit isomorphism of algebraic spaces commutes with the structure morphisms to `S`. -/
theorem extendBaseCounitLeftIso_w {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    (extendBaseCounitLeftIso X).hom ≫ X.hom =
      ((restrictOverFunctor g ⋙ extendBaseOver g).obj X).hom := sorry

/-- The counit isomorphism at a pair `(F', F' ⟶ S)`. -/
def extendBaseCounitAppIso {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over (ofOver (Over.mk g))) :
    (restrictOverFunctor g ⋙ extendBaseOver g).obj X ≅ X :=
  Over.isoMk (extendBaseCounitLeftIso X) (extendBaseCounitLeftIso_w X)

/-- Naturality of the counit components. -/
theorem extendBaseCounitIso_naturality {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y) :
    (restrictOverFunctor g ⋙ extendBaseOver g).map f ≫
        (extendBaseCounitAppIso g Y).hom =
      (extendBaseCounitAppIso g X).hom ≫ f := sorry

/-- The counit isomorphism `restrictOverFunctor g ⋙ extendBaseOver g ≅ 𝟭`. -/
def extendBaseCounitIso {S S' : Scheme.{u}} (g : S ⟶ S') :
    restrictOverFunctor g ⋙ extendBaseOver g ≅ 𝟭 (Over (ofOver (Over.mk g))) :=
  NatIso.ofComponents (fun X ↦ extendBaseCounitAppIso g X)
    (extendBaseCounitIso_naturality g)

end AlgebraicGeometry.AlgebraicSpace
