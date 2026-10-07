module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Fiber
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Basic
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Lemma_78_20_3_Comparison
public import stacks_project.Chap78.Lemma_78_22_1_Isom

/-!
# Explicit `[U/R]`-descent data

This module owns the source-facing payload of a `[U/R]`-descent datum relative to an indexed
family of schemes over `T`: maps into `U` and `R`, source/target/cocycle laws, morphisms, and
pullback along a refinement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite
open Functor
open CategoryTheory.CategoryOfElements

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The member `T_i` of an indexed family over `T`, viewed as a scheme over `S`. -/
def coverOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i : ι) :
    Over S :=
  Over.mk ((family i).hom ≫ T.hom)

/-- The structure morphism `T_i ⟶ T` of a covering member. -/
def coverHom {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i : ι) :
    coverOver family i ⟶ T :=
  Over.homMk (family i).hom rfl

/-- `coverHom family i` is the over-morphism induced by `(family i).hom`. -/
theorem coverOver_hom {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i : ι) :
    coverHom family i = Over.homMk (family i).hom rfl :=
  sorry

/-- The fibre product `T_i ×_T T_j`, viewed as a scheme over `S`. -/
def pairOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    Over S :=
  Over.mk (pullback.fst (family i).hom (family j).hom ≫ (family i).hom ≫ T.hom)

/-- Stacks `pr₀ : T_i ×_T T_j ⟶ T_i`. -/
def pr0 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pairOver family i j ⟶ coverOver family i :=
  Over.homMk (pullback.fst (family i).hom (family j).hom) rfl

/-- Compatibility of `pr1` with the structure morphisms to `S`. -/
theorem pr1_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pullback.snd (family i).hom (family j).hom ≫ (coverOver family j).hom =
      (pairOver family i j).hom :=
  sorry

/-- Stacks `pr₁ : T_i ×_T T_j ⟶ T_j`. -/
def pr1 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j : ι) :
    pairOver family i j ⟶ coverOver family j :=
  Over.homMk (pullback.snd (family i).hom (family j).hom) (pr1_w family i j)

/-- `pr0` is induced by `pullback.fst`. -/
theorem pairOver_pr0 {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr0 family i j = Over.homMk (pullback.fst (family i).hom (family j).hom) rfl :=
  sorry

/-- `pr1` is induced by `pullback.snd`. -/
theorem pairOver_pr1 {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr1 family i j =
      Over.homMk (pullback.snd (family i).hom (family j).hom) (pr1_w family i j) :=
  sorry

/-- The two projections of `T_i ×_T T_j` agree after composing to `T`. -/
theorem pr0_coverHom {S : Scheme.{u}} {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (i j : ι) :
    pr0 family i j ≫ coverHom family i = pr1 family i j ≫ coverHom family j :=
  sorry

/-- The triple fibre product `T_i ×_T T_j ×_T T_k`, as `(T_i ×_T T_j) ×_T T_k` over `S`. -/
def tripleOver {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : Over S :=
  Over.mk
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      (pairOver family i j).hom)

/-- Stacks `pr₀₁ : T_i ×_T T_j ×_T T_k ⟶ T_i ×_T T_j`. -/
def pr01 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family i j :=
  Over.homMk
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    rfl

/-- The two legs of `pr12Scheme` agree over `T`. -/
theorem pr12Scheme_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        pullback.snd (family i).hom (family j).hom) ≫
        (family j).hom =
      pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        (family k).hom :=
  sorry

/-- Underlying scheme map of `pr₁₂`. -/
def pr12Scheme {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : (tripleOver family i j k).left ⟶ (pairOver family j k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      pullback.snd (family i).hom (family j).hom)
    (pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    (pr12Scheme_w family i j k)

/-- `pr12Scheme` lies over `S`. -/
theorem pr12_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    pr12Scheme family i j k ≫ (pairOver family j k).hom = (tripleOver family i j k).hom :=
  sorry

/-- Stacks `pr₁₂ : T_i ×_T T_j ×_T T_k ⟶ T_j ×_T T_k`. -/
def pr12 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family j k :=
  Over.homMk (pr12Scheme family i j k) (pr12_w family i j k)

/-- The two legs of `pr02Scheme` agree over `T`. -/
theorem pr02Scheme_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        pullback.fst (family i).hom (family j).hom) ≫
        (family i).hom =
      pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
          (family k).hom ≫
        (family k).hom :=
  sorry

/-- Underlying scheme map of `pr₀₂`. -/
def pr02Scheme {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) : (tripleOver family i j k).left ⟶ (pairOver family i k).left :=
  pullback.lift
    (pullback.fst (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
        (family k).hom ≫
      pullback.fst (family i).hom (family j).hom)
    (pullback.snd (pullback.fst (family i).hom (family j).hom ≫ (family i).hom)
      (family k).hom)
    (pr02Scheme_w family i j k)

/-- `pr02Scheme` lies over `S`. -/
theorem pr02_w {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (i j k : ι) :
    pr02Scheme family i j k ≫ (pairOver family i k).hom = (tripleOver family i j k).hom :=
  sorry

/-- Stacks `pr₀₂ : T_i ×_T T_j ×_T T_k ⟶ T_i ×_T T_k`. -/
def pr02 {S : Scheme.{u}} {T : Over S} {ι : Type u} (family : ι → Over T.left) (i j k : ι) :
    tripleOver family i j k ⟶ pairOver family i k :=
  Over.homMk (pr02Scheme family i j k) (pr02_w family i j k)

/-- Compose two `X`-valued arrows of `G` by transporting the fibre product of `s` and `t`
along `Over.forget B` and applying `G.c`. Later/earlier is `pullback.fst`/`pullback.snd`. -/
def compArrows {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : AlgebraicSpace S} (later earlier : X ⟶ G.R.left)
    (h : later ≫ G.s.left = earlier ≫ G.t.left) : X ⟶ G.R.left :=
  pullback.lift later earlier h ≫
    (PreservesPullback.iso (Over.forget B) G.s G.t).inv ≫ G.c.left

/-- `compArrows` is the composite of the forgetful pullback comparison with `G.c.left`. -/
theorem compArrows_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {X : AlgebraicSpace S} (later earlier : X ⟶ G.R.left)
    (h : later ≫ G.s.left = earlier ≫ G.t.left) :
    G.compArrows later earlier h =
      pullback.lift later earlier h ≫
        (PreservesPullback.iso (Over.forget B) G.s G.t).inv ≫ G.c.left :=
  sorry

/-- The object `π(u)` of `[U/R]_T` associated to a morphism `u : T ⟶ U`. -/
def atlasObj {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) : (quotientStack G).p.Fiber T :=
  ((atlas G).fiberFunctor T).obj (objOfHom u)

/-- `atlasObj G u` is the image of `objOfHom u` under the fibre functor of `atlas G`. -/
theorem atlasObj_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    atlasObj G u = ((atlas G).fiberFunctor T).obj (objOfHom u) :=
  sorry

/-- Restriction of a fibre object of `[U/R]` along a morphism of schemes over `S`. -/
def fiberRestrict {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) (x : (quotientStack G).p.Fiber T) :
    (quotientStack G).p.Fiber T' :=
  Functor.Chosen.reindexObj (quotientStack G).p f x

/-- `fiberRestrict` is selected-cleavage reindexing of `(quotientStack G).p`. -/
theorem fiberRestrict_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) (x : (quotientStack G).p.Fiber T) :
    fiberRestrict G f x = Functor.Chosen.reindexObj (quotientStack G).p f x :=
  sorry

/-- Restriction of a fibre morphism of `[U/R]` along a morphism of schemes over `S`. -/
def fiberRestrictMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) {x y : (quotientStack G).p.Fiber T} (φ : x ⟶ y) :
    fiberRestrict G f x ⟶ fiberRestrict G f y :=
  Functor.Chosen.reindexMap (quotientStack G).p f φ

/-- `fiberRestrictMap` is selected-cleavage reindexing of fibre morphisms. -/
theorem fiberRestrictMap_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : T' ⟶ T)
    {x y : (quotientStack G).p.Fiber T} (φ : x ⟶ y) :
    fiberRestrictMap G f φ = Functor.Chosen.reindexMap (quotientStack G).p f φ :=
  sorry

/-- Restriction of a fibre isomorphism of `[U/R]` along a morphism of schemes over `S`. -/
def fiberRestrictMapIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) {x y : (quotientStack G).p.Fiber T} (e : x ≅ y) :
    fiberRestrict G f x ≅ fiberRestrict G f y where
  hom := fiberRestrictMap G f e.hom
  inv := fiberRestrictMap G f e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `fiberRestrictMapIso` is `fiberRestrictMap` of the forward map. -/
theorem fiberRestrictMapIso_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : T' ⟶ T)
    {x y : (quotientStack G).p.Fiber T} (e : x ≅ y) :
    (fiberRestrictMapIso G f e).hom = fiberRestrictMap G f e.hom :=
  sorry

/-- The fibre morphism `π(r) : π(s ∘ r) ⟶ π(t ∘ r)` associated to `r : T ⟶ R`. -/
def atlasArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    ((atlasSource G).fiberFunctor T).obj (objOfHom r) ⟶
      ((atlasTarget G).fiberFunctor T).obj (objOfHom r) :=
  (CartesianBasedFunctor.fiberNatTrans (sourceTarget G) T).app (objOfHom r)

/-- `atlasArrow G r` is the fibre component of `sourceTarget G` at `objOfHom r`. -/
theorem atlasArrow_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    atlasArrow G r =
      (CartesianBasedFunctor.fiberNatTrans (sourceTarget G) T).app (objOfHom r) :=
  sorry

/-- The selected reindexing of `objOfHom u` along `f` is the object `objOfHom (ofOverMap f ≫ u)`. -/
def objOfHomReindexIso {S : Scheme.{u}} {X : AlgebraicSpace S} {T T' : Over S}
    (f : T' ⟶ T) (u : ofOver T ⟶ X) :
    objOfHom (ofOverMap f ≫ u) ≅ Chosen.reindexObj (stackInSets X).p f (objOfHom u) :=
  Fiber.isoMk
    (IsStronglyCartesian.DomainIso.ofBaseIso (stackInSets X).p
      (g := Iso.refl T') (h := (Category.id_comp f).symm)
      (Chosen.cartesianHom (stackInSets X).p f (objOfHom u))
      (homMk
          ⟨op T, yonedaEquiv (u : yoneda.obj T ⟶ X.functorOfPoints)⟩
          ⟨op T', yonedaEquiv ((ofOverMap f ≫ u) : yoneda.obj T' ⟶ X.functorOfPoints)⟩
          f.op sorry).op
      (Chosen.cartesianHom.isStronglyCartesian (stackInSets X).p f (objOfHom u))
      sorry)
    sorry

/-- `objOfHomReindexIso` identifies `objOfHom (ofOverMap f ≫ u)` with selected reindexing. -/
theorem objOfHomReindexIso_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {T T' : Over S}
    (f : T' ⟶ T) (u : ofOver T ⟶ X) :
    Nonempty (objOfHom (ofOverMap f ≫ u) ≅
      Chosen.reindexObj (stackInSets X).p f (objOfHom u)) :=
  sorry

/-- Postcomposition with `φ` on `𝒮_X` sends `objOfHom r` to `objOfHom (r ≫ φ)`. -/
def objOfHomMapIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) {T : Over S}
    (r : ofOver T ⟶ X) :
    ((stackInSets.map φ).fiberFunctor T).obj (objOfHom r) ≅ objOfHom (r ≫ φ) :=
  Fiber.isoMk
    (isoMk
        (((stackInSets.map φ).fiberFunctor T).obj (objOfHom r)).1.unop
        (objOfHom (r ≫ φ)).1.unop (Iso.refl _) sorry).op
    sorry

/-- `objOfHomMapIso` is the fibre identification of `stackInSets.map φ` on `objOfHom`. -/
theorem objOfHomMapIso_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) {T : Over S}
    (r : ofOver T ⟶ X) :
    Nonempty (((stackInSets.map φ).fiberFunctor T).obj (objOfHom r) ≅ objOfHom (r ≫ φ)) :=
  sorry

/-- The atlas comparison `f^* π(u) ≅ π(f^* u)` from selected-cleavage reindexing. -/
def atlasReindexIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) (u : ofOver T ⟶ G.U.left) :
    fiberRestrict G f (atlasObj G u) ≅
      ((atlas G).fiberFunctor T').obj
        (Chosen.reindexObj (stackInSets G.U.left).p f (objOfHom u)) :=
  CartesianBasedFunctor.Reindex.mapIso (atlas G)
    (Cleavage.ofIsFibered (stackInSets G.U.left).p)
    (Cleavage.ofIsFibered (quotientStack G).p) f (objOfHom u)

/-- `atlasReindexIso` is `CartesianBasedFunctor.Reindex.mapIso` of `atlas G`. -/
theorem atlasReindexIso_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : T' ⟶ T)
    (u : ofOver T ⟶ G.U.left) :
    atlasReindexIso G f u =
      CartesianBasedFunctor.Reindex.mapIso (atlas G)
        (Cleavage.ofIsFibered (stackInSets G.U.left).p)
        (Cleavage.ofIsFibered (quotientStack G).p) f (objOfHom u) :=
  sorry

/-- The canonical identification `π(u ∘ f) ≅ f^* π(u)`. -/
def atlasObjReindexIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (f : T' ⟶ T) (u : ofOver T ⟶ G.U.left) :
    atlasObj G (ofOverMap f ≫ u) ≅ fiberRestrict G f (atlasObj G u) :=
  ((atlas G).fiberFunctor T').mapIso (objOfHomReindexIso f u) ≪≫
    (atlasReindexIso G f u).symm

/-- `atlasObjReindexIso` factors as `objOfHomReindexIso` followed by `atlasReindexIso`. -/
theorem atlasObjReindexIso_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : T' ⟶ T)
    (u : ofOver T ⟶ G.U.left) :
    atlasObjReindexIso G f u =
      ((atlas G).fiberFunctor T').mapIso (objOfHomReindexIso f u) ≪≫
        (atlasReindexIso G f u).symm :=
  sorry

/-- Forget `π ∘ s` to `π` on the fibre object associated to `r`. -/
def atlasSourceFiberIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    ((atlasSource G).fiberFunctor T).obj (objOfHom r) ≅
      ((atlas G).fiberFunctor T).obj
        (((stackInSets.map G.s.left).fiberFunctor T).obj (objOfHom r)) :=
  Fiber.isoMk (Iso.refl _) sorry

/-- `atlasSourceFiberIso` compares `π ∘ s` with `π` on `objOfHom r`. -/
theorem atlasSourceFiberIso_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (r : ofOver T ⟶ G.R.left) :
    Nonempty
      (((atlasSource G).fiberFunctor T).obj (objOfHom r) ≅
        ((atlas G).fiberFunctor T).obj
          (((stackInSets.map G.s.left).fiberFunctor T).obj (objOfHom r))) :=
  sorry

/-- Forget `π ∘ t` to `π` on the fibre object associated to `r`. -/
def atlasTargetFiberIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (r : ofOver T ⟶ G.R.left) :
    ((atlasTarget G).fiberFunctor T).obj (objOfHom r) ≅
      ((atlas G).fiberFunctor T).obj
        (((stackInSets.map G.t.left).fiberFunctor T).obj (objOfHom r)) :=
  Fiber.isoMk (Iso.refl _) sorry

/-- `atlasTargetFiberIso` compares `π ∘ t` with `π` on `objOfHom r`. -/
theorem atlasTargetFiberIso_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (r : ofOver T ⟶ G.R.left) :
    Nonempty
      (((atlasTarget G).fiberFunctor T).obj (objOfHom r) ≅
        ((atlas G).fiberFunctor T).obj
          (((stackInSets.map G.t.left).fiberFunctor T).obj (objOfHom r))) :=
  sorry

/-- The canonical associator `pr₀^* f_i^* x ≅ pr₁^* f_j^* x`. -/
def overlapAssociator {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (quotientStack G).p.Fiber T) (i j : ι) :
    fiberRestrict G (pr0 family i j) (fiberRestrict G (coverHom family i) x) ≅
      fiberRestrict G (pr1 family i j) (fiberRestrict G (coverHom family j) x) :=
  (Chosen.Reindex.specifiedCompIsoApp (quotientStack G).p
      (coverHom family i) (pr0 family i j)
      (pr0 family i j ≫ coverHom family i) rfl x).symm ≪≫
    Chosen.Reindex.congrIsoApp (quotientStack G).p (pr0_coverHom family i j) x ≪≫
    Chosen.Reindex.specifiedCompIsoApp (quotientStack G).p
      (coverHom family j) (pr1 family i j)
      (pr1 family i j ≫ coverHom family j) rfl x

/-- `overlapAssociator` is the selected-cleavage composite comparison on `pr₀` and `pr₁`. -/
theorem overlapAssociator_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) (x : (quotientStack G).p.Fiber T) (i j : ι) :
    overlapAssociator G family x i j =
      (Chosen.Reindex.specifiedCompIsoApp (quotientStack G).p
          (coverHom family i) (pr0 family i j)
          (pr0 family i j ≫ coverHom family i) rfl x).symm ≪≫
        Chosen.Reindex.congrIsoApp (quotientStack G).p (pr0_coverHom family i j) x ≪≫
        Chosen.Reindex.specifiedCompIsoApp (quotientStack G).p
          (coverHom family j) (pr1 family i j)
          (pr1 family i j ≫ coverHom family j) rfl x :=
  sorry

/-- The canonical source comparison `π(s ∘ r) ≅ pr₀^* π(u)` from the source law. -/
def sourceComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family i) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u) :
    ((atlasSource G).fiberFunctor (pairOver family i j)).obj (objOfHom r) ≅
      fiberRestrict G (pr0 family i j) (atlasObj G u) :=
  atlasSourceFiberIso G r ≪≫
    ((atlas G).fiberFunctor (pairOver family i j)).mapIso
      (objOfHomMapIso G.s.left r ≪≫
        eqToIso (congrArg objOfHom hs) ≪≫ objOfHomReindexIso (pr0 family i j) u) ≪≫
    (atlasReindexIso G (pr0 family i j) u).symm

/-- `sourceComparison` is the composite of `atlasSourceFiberIso`, `objOfHomMapIso`, and
`atlasObjReindexIso`. -/
theorem sourceComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family i) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u) :
    sourceComparison G family u hs =
      atlasSourceFiberIso G r ≪≫
        ((atlas G).fiberFunctor (pairOver family i j)).mapIso
          (objOfHomMapIso G.s.left r ≪≫
            eqToIso (congrArg objOfHom hs) ≪≫ objOfHomReindexIso (pr0 family i j) u) ≪≫
        (atlasReindexIso G (pr0 family i j) u).symm :=
  sorry

/-- The canonical target comparison `π(t ∘ r) ≅ pr₁^* π(u)` from the target law. -/
def targetComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family j) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u) :
    ((atlasTarget G).fiberFunctor (pairOver family i j)).obj (objOfHom r) ≅
      fiberRestrict G (pr1 family i j) (atlasObj G u) :=
  atlasTargetFiberIso G r ≪≫
    ((atlas G).fiberFunctor (pairOver family i j)).mapIso
      (objOfHomMapIso G.t.left r ≪≫
        eqToIso (congrArg objOfHom ht) ≪≫ objOfHomReindexIso (pr1 family i j) u) ≪≫
    (atlasReindexIso G (pr1 family i j) u).symm

/-- `targetComparison` is the composite of `atlasTargetFiberIso`, `objOfHomMapIso`, and
`atlasObjReindexIso`. -/
theorem targetComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} {ι : Type u}
    (family : ι → Over T.left) {i j : ι}
    (u : ofOver (coverOver family j) ⟶ G.U.left)
    {r : ofOver (pairOver family i j) ⟶ G.R.left}
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u) :
    targetComparison G family u ht =
      atlasTargetFiberIso G r ≪≫
        ((atlas G).fiberFunctor (pairOver family i j)).mapIso
          (objOfHomMapIso G.t.left r ≪≫
            eqToIso (congrArg objOfHom ht) ≪≫ objOfHomReindexIso (pr1 family i j) u) ≪≫
        (atlasReindexIso G (pr1 family i j) u).symm :=
  sorry

/-- The canonical comparison `π(s ∘ r) ≅ π(u)` on a covering member from `u = s ∘ r`. -/
def sourceHomComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (hs : u = rR ≫ G.s.left) :
    ((atlasSource G).fiberFunctor T).obj (objOfHom rR) ≅ atlasObj G u :=
  atlasSourceFiberIso G rR ≪≫
    ((atlas G).fiberFunctor T).mapIso
      (objOfHomMapIso G.s.left rR ≪≫ eqToIso (congrArg objOfHom hs.symm))

/-- `sourceHomComparison` is the composite of `atlasSourceFiberIso` and `objOfHomMapIso`. -/
theorem sourceHomComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S}
    (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (hs : u = rR ≫ G.s.left) :
    sourceHomComparison G u rR hs =
      atlasSourceFiberIso G rR ≪≫
        ((atlas G).fiberFunctor T).mapIso
          (objOfHomMapIso G.s.left rR ≪≫ eqToIso (congrArg objOfHom hs.symm)) :=
  sorry

/-- The canonical comparison `π(t ∘ r) ≅ π(u)` on a covering member from `u = t ∘ r`. -/
def targetHomComparison {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (ht : u = rR ≫ G.t.left) :
    ((atlasTarget G).fiberFunctor T).obj (objOfHom rR) ≅ atlasObj G u :=
  atlasTargetFiberIso G rR ≪≫
    ((atlas G).fiberFunctor T).mapIso
      (objOfHomMapIso G.t.left rR ≪≫ eqToIso (congrArg objOfHom ht.symm))

/-- `targetHomComparison` is the composite of `atlasTargetFiberIso` and `objOfHomMapIso`. -/
theorem targetHomComparison_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S}
    (u : ofOver T ⟶ G.U.left) (rR : ofOver T ⟶ G.R.left)
    (ht : u = rR ≫ G.t.left) :
    targetHomComparison G u rR ht =
      atlasTargetFiberIso G rR ≪≫
        ((atlas G).fiberFunctor T).mapIso
          (objOfHomMapIso G.t.left rR ≪≫ eqToIso (congrArg objOfHom ht.symm)) :=
  sorry

/-- A `[U/R]`-descent datum relative to an indexed family of schemes over `T`. -/
structure DescentDatum {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left) where
  /-- The object maps `u_i : T_i ⟶ U`. -/
  u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left
  /-- The arrow maps `r_ij : T_i ×_T T_j ⟶ R`. -/
  r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left
  /-- Source law: `s ∘ r_ij = u_i ∘ pr₀`. -/
  source : ∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i
  /-- Target law: `t ∘ r_ij = u_j ∘ pr₁`. -/
  target : ∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j
  /-- Cocycle law: `c ∘ (r_jk ∘ pr₁₂, r_ij ∘ pr₀₁) = r_ik ∘ pr₀₂`. -/
  cocycle :
    ∀ i j k
      (h :
        (ofOverMap (pr12 family i j k) ≫ r j k) ≫ G.s.left =
          (ofOverMap (pr01 family i j k) ≫ r i j) ≫ G.t.left),
      G.compArrows (ofOverMap (pr12 family i j k) ≫ r j k)
          (ofOverMap (pr01 family i j k) ≫ r i j) h =
        ofOverMap (pr02 family i j k) ≫ r i k

namespace DescentDatum

/-- Assemble a descent datum from object maps, arrow maps, and the three laws. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left)
    (hsource : ∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
    (htarget : ∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j)
    (hcocycle :
      ∀ i j k
        (h :
          (ofOverMap (pr12 family i j k) ≫ r j k) ≫ G.s.left =
            (ofOverMap (pr01 family i j k) ≫ r i j) ≫ G.t.left),
        G.compArrows (ofOverMap (pr12 family i j k) ≫ r j k)
            (ofOverMap (pr01 family i j k) ≫ r i j) h =
          ofOverMap (pr02 family i j k) ≫ r i k) :
    DescentDatum G family where
  u := u
  r := r
  source := hsource
  target := htarget
  cocycle := hcocycle

/-- The object maps of `of` are the supplied maps. -/
theorem of_u {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (r : ∀ i j, ofOver (pairOver family i j) ⟶ G.R.left)
    (hsource : ∀ i j, r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
    (htarget : ∀ i j, r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j)
    (hcocycle :
      ∀ i j k
        (h :
          (ofOverMap (pr12 family i j k) ≫ r j k) ≫ G.s.left =
            (ofOverMap (pr01 family i j k) ≫ r i j) ≫ G.t.left),
        G.compArrows (ofOverMap (pr12 family i j k) ≫ r j k)
            (ofOverMap (pr01 family i j k) ≫ r i j) h =
          ofOverMap (pr02 family i j k) ≫ r i k) :
    (of u r hsource htarget hcocycle).u = u :=
  sorry

/-- Source, target, and cocycle laws of a descent datum. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    (∀ i j, D.r i j ≫ G.s.left = ofOverMap (pr0 family i j) ≫ D.u i) ∧
      (∀ i j, D.r i j ≫ G.t.left = ofOverMap (pr1 family i j) ≫ D.u j) ∧
        ∀ i j k
          (h :
            (ofOverMap (pr12 family i j k) ≫ D.r j k) ≫ G.s.left =
              (ofOverMap (pr01 family i j k) ≫ D.r i j) ≫ G.t.left),
          G.compArrows (ofOverMap (pr12 family i j k) ≫ D.r j k)
              (ofOverMap (pr01 family i j k) ≫ D.r i j) h =
            ofOverMap (pr02 family i j k) ≫ D.r i k :=
  sorry

/-- The identity covering `{T ⟶ T}` as a `PUnit`-indexed family. -/
def identityFamily {S : Scheme.{u}} (T : Over S) : PUnit.{u + 1} → Over T.left :=
  fun _ ↦ Over.mk (𝟙 T.left)

/-- The identity covering member is `T` over `S`. -/
def identityCoverHom {S : Scheme.{u}} (T : Over S) :
    coverOver (identityFamily T) PUnit.unit ⟶ T :=
  Over.homMk (𝟙 T.left) rfl

/-- The pair of the identity covering maps to `T` by `pr₀`. -/
def identityPairHom {S : Scheme.{u}} (T : Over S) :
    pairOver (identityFamily T) PUnit.unit PUnit.unit ⟶ T :=
  Over.homMk (pullback.fst (𝟙 T.left) (𝟙 T.left) ≫ 𝟙 T.left) rfl

/-- The trivial descent datum of a morphism `T ⟶ U` on the identity covering. -/
def trivial {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    DescentDatum G (identityFamily T) where
  u := fun _ ↦ ofOverMap (identityCoverHom T) ≫ u
  r := fun _ _ ↦ ofOverMap (identityPairHom T) ≫ u ≫ G.e.left
  source := sorry
  target := sorry
  cocycle := sorry

/-- The object map of `trivial G u` is `u` after identifying the identity covering with `T`. -/
theorem trivial_u {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (u : ofOver T ⟶ G.U.left) :
    (trivial G u).u PUnit.unit = ofOverMap (identityCoverHom T) ≫ u :=
  sorry

/-- Compatibility of a covering member of a refinement with the structure maps to `S`. -/
theorem coverMap_w {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (φ j).left ≫ (coverOver family (α j)).hom = (coverOver family' j).hom :=
  sorry

/-- The morphism `T'_j ⟶ T_{α(j)}` of a refinement, as a map of schemes over `S`. -/
def coverMap {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    coverOver family' j ⟶ coverOver family (α j) :=
  Over.homMk (φ j).left (coverMap_w α φ j)

/-- A refinement map commutes with the structure morphisms to `T`. -/
theorem coverMap_coverHom {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    coverMap α φ j ≫ coverHom family (α j) = coverHom family' j :=
  sorry

/-- Underlying scheme map of a pairwise refinement. -/
def pairMapScheme {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    (pairOver family' j j').left ⟶ (pairOver family (α j) (α j')).left :=
  pullback.map (family' j).hom (family' j').hom (family (α j)).hom (family (α j')).hom
    (φ j).left (φ j').left (𝟙 T.left)
    ((Category.comp_id (family' j).hom).trans (Over.w (φ j)).symm)
    ((Category.comp_id (family' j').hom).trans (Over.w (φ j')).symm)

/-- `pairMapScheme` lies over `S`. -/
theorem pairMap_w {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    pairMapScheme α φ j j' ≫ (pairOver family (α j) (α j')).hom =
      (pairOver family' j j').hom :=
  sorry

/-- The morphism `T'_j ×_T T'_{j'} ⟶ T_{α(j)} ×_T T_{α(j')}` of a refinement. -/
def pairMap {S : Scheme.{u}} {T : Over S} {ι ι' : Type u}
    {family : ι → Over T.left} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    pairOver family' j j' ⟶ pairOver family (α j) (α j') :=
  Over.homMk (pairMapScheme α φ j j') (pairMap_w α φ j j')

/-- Pullback of a descent datum along a refinement `α, φ` of indexed families over `T`. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    DescentDatum G family' where
  u := fun j ↦ ofOverMap (coverMap α φ j) ≫ D.u (α j)
  r := fun j j' ↦ ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j')
  source := sorry
  target := sorry
  cocycle := sorry

/-- Object maps of a pulled-back descent datum are `u_{α(j)} ∘ φ_j`. -/
theorem pullback_u {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (D.pullback α φ).u j = ofOverMap (coverMap α φ j) ≫ D.u (α j) :=
  sorry

/-- Arrow maps of a pulled-back descent datum are `r_{α(j)α(j')} ∘ (φ_j × φ_{j'})`. -/
theorem pullback_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family)
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j j' : ι') :
    (D.pullback α φ).r j j' = ofOverMap (pairMap α φ j j') ≫ D.r (α j) (α j') :=
  sorry

/-- A morphism of `[U/R]`-descent data over a fixed indexed family. -/
structure Hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (D D' : DescentDatum G family) where
  /-- The component arrows `r_i : T_i ⟶ R`. -/
  r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left
  /-- Source law `(α)`: `u_i = s ∘ r_i`. -/
  source : ∀ i, D.u i = r i ≫ G.s.left
  /-- Target law `(α)`: `u'_i = t ∘ r_i`. -/
  target : ∀ i, D'.u i = r i ≫ G.t.left
  /-- Compatibility `(β)`: `c ∘ (r'_ij, r_i ∘ pr₀) = c ∘ (r_j ∘ pr₁, r_ij)`. -/
  compat :
    ∀ i j
      (h₁ :
        D'.r i j ≫ G.s.left =
          (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
      (h₂ :
        (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
          D.r i j ≫ G.t.left),
      G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
        G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂

namespace Hom

/-- Assemble a morphism of descent data from component arrows and the two laws. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family}
    (r : ∀ i, ofOver (coverOver family i) ⟶ G.R.left)
    (hsource : ∀ i, D.u i = r i ≫ G.s.left)
    (htarget : ∀ i, D'.u i = r i ≫ G.t.left)
    (hcompat :
      ∀ i j
        (h₁ :
          D'.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ r j) (D.r i j) h₂) :
    Hom D D' where
  r := r
  source := hsource
  target := htarget
  compat := hcompat

/-- Source and compatibility laws of a morphism of descent data. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    (∀ i, D.u i = ψ.r i ≫ G.s.left ∧ D'.u i = ψ.r i ≫ G.t.left) ∧
      ∀ i j
        (h₁ :
          D'.r i j ≫ G.s.left =
            (ofOverMap (pr0 family i j) ≫ ψ.r i) ≫ G.t.left)
        (h₂ :
          (ofOverMap (pr1 family i j) ≫ ψ.r j) ≫ G.s.left =
            D.r i j ≫ G.t.left),
        G.compArrows (D'.r i j) (ofOverMap (pr0 family i j) ≫ ψ.r i) h₁ =
          G.compArrows (ofOverMap (pr1 family i j) ≫ ψ.r j) (D.r i j) h₂ :=
  sorry

/-- Identity morphism of a descent datum, with components `e ∘ u_i`. -/
def id {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) :
    Hom D D where
  r := fun i ↦ D.u i ≫ G.e.left
  source := sorry
  target := sorry
  compat := sorry

/-- Components of the identity morphism are `e ∘ u_i`. -/
theorem id_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left} (D : DescentDatum G family) (i : ι) :
    (Hom.id D).r i = D.u i ≫ G.e.left :=
  sorry

/-- Composability of component arrows of two morphisms of descent data. -/
theorem comp_composable {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') (i : ι) :
    ψ'.r i ≫ G.s.left = ψ.r i ≫ G.t.left :=
  sorry

/-- Composition of morphisms of descent data, with components `c ∘ (r'_i, r_i)`. -/
def comp {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' D'' : DescentDatum G family} (ψ : Hom D D') (ψ' : Hom D' D'') :
    Hom D D'' where
  r := fun i ↦ G.compArrows (ψ'.r i) (ψ.r i) (comp_composable ψ ψ' i)
  source := sorry
  target := sorry
  compat := sorry

/-- Inverse of a morphism of descent data, with components `i ∘ r_i`. -/
def inv {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') :
    Hom D' D where
  r := fun i ↦ ψ.r i ≫ G.i.left
  source := sorry
  target := sorry
  compat := sorry

/-- Components of the inverse morphism are `i ∘ r_i`. -/
theorem inv_r {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D') (i : ι) :
    (ψ.inv).r i = ψ.r i ≫ G.i.left :=
  sorry

/-- Pullback of a morphism of descent data along a refinement of indexed families. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : Hom D D')
    {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    Hom (D.pullback α φ) (D'.pullback α φ) where
  r := fun j ↦ ofOverMap (coverMap α φ j) ≫ ψ.r (α j)
  source := sorry
  target := sorry
  compat := sorry

end Hom

end DescentDatum

/-- The overlap arrow `r` realises the canonical composite of the given fibre isomorphisms as
`π(r)`, after the source and target laws. -/
def IsPiArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (quotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ fiberRestrict G (coverHom family i) x)
    {i j : ι} (r : ofOver (pairOver family i j) ⟶ G.R.left) : Prop :=
  ∃ (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
    (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j),
    (sourceComparison G family (u i) hs).hom ≫
        fiberRestrictMap G (pr0 family i j) (e i).hom ≫
        (overlapAssociator G family x i j).hom ≫
        fiberRestrictMap G (pr1 family i j) (e j).inv ≫
        (targetComparison G family (u j) ht).inv =
      atlasArrow G r

/-- `IsPiArrow` records the source and target laws together with equality of `atlasArrow r`
against the named canonical composite. -/
theorem isPiArrow_spec {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (quotientStack G).p.Fiber T)
    (u : ∀ i, ofOver (coverOver family i) ⟶ G.U.left)
    (e : ∀ i, atlasObj G (u i) ≅ fiberRestrict G (coverHom family i) x)
    {i j : ι} (r : ofOver (pairOver family i j) ⟶ G.R.left) :
    IsPiArrow G family x u e r ↔
      ∃ (hs : r ≫ G.s.left = ofOverMap (pr0 family i j) ≫ u i)
        (ht : r ≫ G.t.left = ofOverMap (pr1 family i j) ≫ u j),
        (sourceComparison G family (u i) hs).hom ≫
            fiberRestrictMap G (pr0 family i j) (e i).hom ≫
            (overlapAssociator G family x i j).hom ≫
            fiberRestrictMap G (pr1 family i j) (e j).inv ≫
            (targetComparison G family (u j) ht).inv =
          atlasArrow G r :=
  sorry

/-- An object of `[U/R]_T` corresponds to a `[U/R]`-descent datum when each restriction is
`π(u_i)` via chosen fibre isomorphisms and each overlap isomorphism is `π(r_ij)`. -/
structure Corresponds {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (quotientStack G).p.Fiber T) (D : DescentDatum G family) where
  /-- The fibre isomorphisms `π(u_i) ≅ f_i^* x`. -/
  e : ∀ i, atlasObj G (D.u i) ≅ fiberRestrict G (coverHom family i) x
  /-- Each overlap arrow realises the named canonical composite as `π(r_ij)`. -/
  overlap : ∀ i j, IsPiArrow G family x D.u e (D.r i j)

namespace Corresponds

/-- Assemble a correspondence from fibre isomorphisms whose overlap composites equal `π(r_ij)`. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (x : (quotientStack G).p.Fiber T) (D : DescentDatum G family)
    (e : ∀ i, atlasObj G (D.u i) ≅ fiberRestrict G (coverHom family i) x)
    (h : ∀ i j, IsPiArrow G family x D.u e (D.r i j)) :
    Corresponds G family x D where
  e := e
  overlap := h

/-- The fibre isomorphisms of `of` are the supplied isomorphisms. -/
theorem of_e {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    (x : (quotientStack G).p.Fiber T) (D : DescentDatum G family)
    (e : ∀ i, atlasObj G (D.u i) ≅ fiberRestrict G (coverHom family i) x)
    (h : ∀ i j, IsPiArrow G family x D.u e (D.r i j)) :
    (of x D e h).e = e :=
  sorry

/-- A correspondence supplies fibre isomorphisms realising each overlap arrow as `π(r_ij)`. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (quotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) :
    ∀ i j, IsPiArrow G family x D.u h.e (D.r i j) :=
  sorry

/-- Pull a correspondence back along a refinement of indexed families. -/
def pullback {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (quotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) :
    Corresponds G family' x (D.pullback α φ) where
  e := fun j ↦
    atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
      fiberRestrictMapIso G (DescentDatum.coverMap α φ j) (h.e (α j)) ≪≫
      (Chosen.Reindex.specifiedCompIsoApp (quotientStack G).p
          (coverHom family (α j)) (DescentDatum.coverMap α φ j)
          (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
      Chosen.Reindex.congrIsoApp (quotientStack G).p
        (DescentDatum.coverMap_coverHom α φ j) x
  overlap := sorry

/-- The pulled-back fibre isomorphism at `j` is the reindexing of `h.e (α j)` along `φ_j`. -/
theorem pullback_e {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {x : (quotientStack G).p.Fiber T} {D : DescentDatum G family}
    (h : Corresponds G family x D) {ι' : Type u} {family' : ι' → Over T.left}
    (α : ι' → ι) (φ : ∀ j, family' j ⟶ family (α j)) (j : ι') :
    (h.pullback α φ).e j =
      atlasObjReindexIso G (DescentDatum.coverMap α φ j) (D.u (α j)) ≪≫
        fiberRestrictMapIso G (DescentDatum.coverMap α φ j) (h.e (α j)) ≪≫
        (Chosen.Reindex.specifiedCompIsoApp (quotientStack G).p
            (coverHom family (α j)) (DescentDatum.coverMap α φ j)
            (DescentDatum.coverMap α φ j ≫ coverHom family (α j)) rfl x).symm ≪≫
        Chosen.Reindex.congrIsoApp (quotientStack G).p
          (DescentDatum.coverMap_coverHom α φ j) x :=
  sorry

end Corresponds

/-- Unfolding of `Corresponds` as chosen fibre isomorphisms realising the overlap arrows as
`π(r_ij)`. -/
theorem corresponds_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} {ι : Type u} (family : ι → Over T.left)
    (x : (quotientStack G).p.Fiber T) (D : DescentDatum G family) :
    Nonempty (Corresponds G family x D) ↔
      ∃ e : ∀ i, atlasObj G (D.u i) ≅ fiberRestrict G (coverHom family i) x,
        ∀ i j, IsPiArrow G family x D.u e (D.r i j) :=
  sorry

/-- A morphism of descent data agrees with a fibre morphism when each component is `π(r_i)`
after conjugating by the chosen correspondence isomorphisms. -/
def DescentDatum.Hom.agreesWith {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : DescentDatum.Hom D D')
    {x y : (quotientStack G).p.Fiber T}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') (φ : x ⟶ y) : Prop :=
  ∀ i,
    (sourceHomComparison G (D.u i) (ψ.r i) (ψ.source i)).hom ≫
        (hx.e i).hom ≫ fiberRestrictMap G (coverHom family i) φ ≫ (hy.e i).inv ≫
        (targetHomComparison G (D'.u i) (ψ.r i) (ψ.target i)).inv =
      atlasArrow G (ψ.r i)

/-- `agreesWith` is conjugation of the restricted fibre morphism by the chosen correspondence
isomorphisms. -/
theorem DescentDatum.Hom.agreesWith_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S} {ι : Type u} {family : ι → Over T.left}
    {D D' : DescentDatum G family} (ψ : DescentDatum.Hom D D')
    {x y : (quotientStack G).p.Fiber T}
    (hx : Corresponds G family x D) (hy : Corresponds G family y D') (φ : x ⟶ y) :
    ψ.agreesWith hx hy φ ↔
      ∀ i,
        (sourceHomComparison G (D.u i) (ψ.r i) (ψ.source i)).hom ≫
            (hx.e i).hom ≫ fiberRestrictMap G (coverHom family i) φ ≫ (hy.e i).inv ≫
            (targetHomComparison G (D'.u i) (ψ.r i) (ψ.target i)).inv =
          atlasArrow G (ψ.r i) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
