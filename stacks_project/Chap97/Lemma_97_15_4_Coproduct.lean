/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.Topology.Clopen
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence
public import stacks_project.Chap97.Lemma_97_15_4_Lci

/-!
# Countable coproduct of LCI Hilbert stacks

The disjoint union `∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴)` is the stack in groupoids whose
objects over a test scheme `T` are pairwise disjoint clopen pieces of `T`,
indexed by `{n : ℕ // 0 < n}` and covering `T`, together with an object of
`H_{n,lci}(𝒳/𝒴)` over each piece. The forgetful 1-morphism to `𝒴` is obtained
by gluing the images of `lciForgetToY` along that clopen cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The empty open subscheme of a scheme is an empty scheme. -/
instance {X : Scheme.{u}} : IsEmpty (⊥ : X.Opens).toScheme :=
  inferInstanceAs (IsEmpty (∅ : Set X))

/-- The empty open of a test scheme over `S` is an empty object of `Over S`. -/
instance {S : Scheme.{u}} (T : Over S) :
    IsEmpty (Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom)).left :=
  inferInstanceAs (IsEmpty (⊥ : T.left.Opens).toScheme)

end AlgebraicGeometry

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The restricted LCI projection is fibered in groupoids. -/
instance lciP.instIsFiberedInGroupoids (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    Functor.IsFibered.InGroupoids (lciP F d) :=
  (lciP_isStack F d).toInGroupoids

/-- The restricted LCI projection is a stack in groupoids. -/
instance lciP.instIsStackInGroupoids (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (lciP F d) :=
  lciP_isStack F d

/-- The restricted LCI projection is a fibered category. -/
instance lciP.instIsFibered (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    (lciP F d).IsFibered :=
  (inferInstance : Functor.IsFibered.InGroupoids (lciP F d)).toIsFibered

/-- The coproduct index `d ≥ 1`. -/
abbrev lciCoproductIndex : Type :=
  {n : ℕ // 0 < n}

/-- A coproduct index is a positive natural number. -/
theorem lciCoproductIndex.pos (i : lciCoproductIndex) : 0 < i.val :=
  sorry

/-- The empty piece of a test scheme, as an object of `Over S`. -/
abbrev emptyPieceOver (T : Over S) : Over S :=
  Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom)

/-- The empty piece of a test scheme is an empty scheme. -/
instance emptyPieceOver.isEmpty (T : Over S) : IsEmpty (emptyPieceOver T).left :=
  inferInstanceAs (IsEmpty (⊥ : T.left.Opens).toScheme)

/-- The top open of a test scheme, as an object of `Over S`. -/
abbrev topOpenOver (T : Over S) : Over S :=
  Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom)

/-- The open immersion of the top open; its underlying scheme map is `Scheme.topIso`. -/
def topOpenHom (T : Over S) : topOpenOver T ⟶ T :=
  Over.homMk (Scheme.topIso T.left).hom

/-- The underlying scheme map of `topOpenHom` is `Scheme.topIso`. -/
theorem topOpenHom_left (T : Over S) :
    (topOpenHom T).left = (Scheme.topIso T.left).hom :=
  sorry

/-- Conjugating a test-scheme morphism by `Scheme.topIso` preserves the structure morphism to
`S`. -/
theorem topOpenOverMap_w {T T' : Over S} (f : T ⟶ T') :
    ((Scheme.topIso T.left).hom ≫ f.left ≫ (Scheme.topIso T'.left).inv) ≫
      (topOpenOver T').hom = (topOpenOver T).hom :=
  sorry

/-- A morphism of test schemes induces a morphism of their top opens, using `Scheme.topIso`
only as the isomorphism `↑⊤ ≅ T.left`. -/
def topOpenOverMap {T T' : Over S} (f : T ⟶ T') :
    topOpenOver T ⟶ topOpenOver T' :=
  Over.homMk
    ((Scheme.topIso T.left).hom ≫ f.left ≫ (Scheme.topIso T'.left).inv)
    (topOpenOverMap_w f)

/-- The unique morphism in `Over S` out of an empty test scheme. -/
def emptyOverHom (T U : Over S) [IsEmpty T.left] : T ⟶ U :=
  Over.homMk (isInitialOfIsEmpty.to U.left)
    (isInitialOfIsEmpty.hom_ext (isInitialOfIsEmpty.to U.left ≫ U.hom) T.hom)

/-- The unique empty-scheme morphism in `Over S` is the unique map of underlying
empty schemes. -/
theorem emptyOverHom_left (T U : Over S) [IsEmpty T.left] :
    (emptyOverHom T U).left = isInitialOfIsEmpty.to U.left :=
  sorry

/-- The empty covering family of objects of `Over S`. -/
def emptyCoverObjs : PEmpty.{u + 1} → Over S :=
  fun i ↦ nomatch i

/-- The empty covering family of arrows into a test scheme. -/
def emptyCoverHoms (T : Over S) :
    ∀ i : PEmpty.{u + 1}, emptyCoverObjs i ⟶ T :=
  fun i ↦ nomatch i

/-- The empty family of arrows covers an empty test scheme in the big fppf topology. -/
theorem emptyArrows_cover_mem (T : Over S) [IsEmpty T.left] :
    Sieve.ofArrows emptyCoverObjs (emptyCoverHoms T) ∈
      Scheme.fppfTopology.over S T :=
  sorry

/-- Empty descent data for a fibered projection over an empty test scheme. -/
def emptyDescentData {𝒮 : Type (u + 1)} [Category.{u} 𝒮]
    (p : 𝒮 ⥤ Over S) [p.IsFibered] (T : Over S) :
    (fiberPseudofunctor p).DescentData (emptyCoverHoms T) where
  obj i := nomatch i
  hom _ _ i1 := nomatch i1
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The unique morphism between descent data for an empty covering family. -/
def emptyDescentHom {𝒮 : Type (u + 1)} [Category.{u} 𝒮]
    (p : 𝒮 ⥤ Over S) [p.IsFibered] (T : Over S)
    (D₁ D₂ : (fiberPseudofunctor p).DescentData (emptyCoverHoms T)) :
    D₁ ⟶ D₂ where
  hom i := nomatch i

/-- A morphism in the fibre over an empty test scheme, obtained by fully faithful descent
along the empty cover. -/
def emptyFiberHom {𝒮 : Type (u + 1)} [Category.{u} 𝒮]
    (p : 𝒮 ⥤ Over S) [IsStack.InGroupoids (Scheme.fppfTopology.over S) p]
    (T : Over S) [IsEmpty T.left] (x z : p.Fiber T) : x ⟶ z :=
  let F := (fiberPseudofunctor p).toDescentData (emptyCoverHoms T)
  let hEq : F.IsEquivalence :=
    Pseudofunctor.isEquivalence_toDescentData
      (fiberPseudofunctor p) (emptyCoverHoms T) (emptyArrows_cover_mem T)
  (@FullyFaithful.ofFullyFaithful _ _ _ _ F hEq.full hEq.faithful).preimage
    (emptyDescentHom p T (F.obj x) (F.obj z))

/-- An object of a stack in groupoids over an empty test scheme, obtained by descent along
the empty cover of that stack (not of `lciP`). -/
def emptyStackFiber
    (𝒵 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S))
    (T : Over S) [IsEmpty T.left] :
    𝒵.p.Fiber T :=
  @objPreimage _ _ _ _ _
    (Pseudofunctor.isEquivalence_toDescentData
        (fiberPseudofunctor 𝒵.p) (emptyCoverHoms T)
        (emptyArrows_cover_mem T)).essSurj
    (emptyDescentData 𝒵.p T)

/-- The unique isomorphism between fibres of a stack projection over an empty test scheme. -/
def emptyFiberIso {𝒮 : Type (u + 1)} [Category.{u} 𝒮]
    (p : 𝒮 ⥤ Over S) [IsStack.InGroupoids (Scheme.fppfTopology.over S) p]
    (T : Over S) [IsEmpty T.left] (x z : p.Fiber T) : x ≅ z where
  hom := emptyFiberHom p T x z
  inv := emptyFiberHom p T z x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Over an empty test scheme, the identity morphism is finite locally free of any rank. -/
theorem emptyOver_isFiniteLocallyFreeOfRank (T : Over S) [IsEmpty T.left] (d : ℕ) :
    IsFiniteLocallyFreeOfRank (𝟙 T.left) d :=
  sorry

/-- The identity of an empty test scheme, as a morphism of `Over S`. -/
def emptyOverId (T : Over S) : T ⟶ T :=
  Over.homMk (𝟙 T.left)

/-- The canonical Hilbert quintuple of degree `d` over an empty test scheme: both `U` and `Z`
are that empty scheme, and the fibre objects of `𝒳` and `𝒴` come from empty-cover descent of
those stacks. Rank, fibre-isomorphism, and LCI proofs may remain deferred. -/
def emptyHilbertObj (F : 𝒳 ⟶ 𝒴) (d : ℕ) (T : Over S) [IsEmpty T.left] :
    Obj (asGroupoidsOverMor F) d :=
  Obj.of T T (emptyOverId T) (emptyOver_isFiniteLocallyFreeOfRank T d)
    (emptyStackFiber 𝒴 T) (emptyStackFiber 𝒳 T)
    (emptyFiberIso 𝒴.p T (restrictObj (emptyStackFiber 𝒴 T) (emptyOverId T))
      ((fiberFunctor (asGroupoidsOverMor F) T).obj (emptyStackFiber 𝒳 T)))

/-- The empty-scheme Hilbert quintuple has test scheme `T`. -/
theorem emptyHilbertObj_U (F : 𝒳 ⟶ 𝒴) (d : ℕ) (T : Over S) [IsEmpty T.left] :
    (emptyHilbertObj F d T).U = T :=
  sorry

/-- The empty-scheme Hilbert quintuple lies in the LCI locus. -/
theorem emptyHilbertObj_isLci (F : 𝒳 ⟶ 𝒴) (d : ℕ) (T : Over S) [IsEmpty T.left] :
    Obj.IsLci (asGroupoidsOverMor F) (emptyHilbertObj F d T) :=
  sorry

/-- The canonical object of `H_{d,lci}(𝒳/𝒴)` over an empty test scheme, as an explicit
Hilbert quintuple rather than a descent preimage of `lciP`. -/
def emptyLciObj (F : 𝒳 ⟶ 𝒴) (d : ℕ) (T : Over S) [IsEmpty T.left] :
    (lci (asGroupoidsOverMor F) d).FullSubcategory where
  obj := emptyHilbertObj F d T
  property := emptyHilbertObj_isLci F d T

/-- The canonical empty-scheme object of `H_{d,lci}` lies over the given empty test scheme. -/
theorem emptyLciObj_p (F : 𝒳 ⟶ 𝒴) (d : ℕ) (T : Over S) [IsEmpty T.left] :
    (lciP F d).obj (emptyLciObj F d T) = T :=
  sorry

/-- The empty-piece object of `Over S` is the open of `⊥` in the test scheme. -/
theorem emptyPieceOver_eq (T : Over S) :
    emptyPieceOver T = Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom) :=
  sorry

/-- The identity square of empty-scheme morphisms commutes. -/
theorem emptyHilbertHom_over_comm (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    (emptyHilbertObj F d T).π ≫ f = f ≫ (emptyHilbertObj F d T').π :=
  sorry

/-- The identity square of empty-scheme morphisms is a pullback. -/
theorem emptyHilbertHom_isPullback (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    IsPullback f.left (emptyHilbertObj F d T).π.left
      (emptyHilbertObj F d T').π.left f.left :=
  sorry

/-- The source square of fibre isomorphisms for an empty-scheme Hilbert morphism commutes. -/
theorem emptyHilbertHom_comm (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    @HomCompatible S (asGroupoidsOver 𝒳) (asGroupoidsOver 𝒴) (asGroupoidsOverMor F) d
      (emptyHilbertObj F d T) (emptyHilbertObj F d T') f f
      (emptyHilbertHom_over_comm F d f)
      (emptyFiberIso 𝒴.p T (emptyHilbertObj F d T).y
        (restrictObj (emptyHilbertObj F d T').y f))
      (emptyFiberIso 𝒳.p T (emptyHilbertObj F d T).x
        (restrictObj (emptyHilbertObj F d T').x f)) :=
  sorry

/-- An explicit Hilbert morphism of empty-scheme quintuples, with unique fibre isomorphisms
over the empty test scheme. -/
def emptyHilbertHom (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    emptyHilbertObj F d T ⟶ emptyHilbertObj F d T' :=
  Hom.homMk f f (emptyHilbertHom_over_comm F d f) (emptyHilbertHom_isPullback F d f)
    (emptyFiberIso 𝒴.p T (emptyHilbertObj F d T).y
      (restrictObj (emptyHilbertObj F d T').y f))
    (emptyFiberIso 𝒳.p T (emptyHilbertObj F d T).x
      (restrictObj (emptyHilbertObj F d T').x f))
    (emptyHilbertHom_comm F d f)

/-- Functoriality of the canonical empty-scheme object of `H_{d,lci}` along a morphism of
empty test schemes. -/
def emptyLciMap (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    emptyLciObj F d T ⟶ emptyLciObj F d T' :=
  InducedCategory.homMk (emptyHilbertHom F d f)

/-- The canonical empty-scheme morphism of `H_{d,lci}` lies over the given empty-scheme
morphism. -/
theorem emptyLciMap_p (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    (lciP F d).map (emptyLciMap F d f) =
      eqToHom (emptyLciObj_p F d T) ≫ f ≫
        eqToHom (emptyLciObj_p F d T').symm :=
  sorry

/-- The cartesian pullback of an LCI Hilbert object along the top-open immersion of its
test scheme. The resulting object lies over `Over.mk (⊤.ι ≫ U.hom)`, not over `U`. -/
def lciPullbackTop (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lci (asGroupoidsOverMor F) d).FullSubcategory :=
  IsPreFibered.pullbackObj (p := lciP F d) rfl (topOpenHom ((lciP F d).obj ξ))

/-- The top-open pullback of an LCI Hilbert object lies over the top open of its test scheme. -/
theorem lciPullbackTop_p (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciP F d).obj (lciPullbackTop F ξ) = topOpenOver ((lciP F d).obj ξ) :=
  sorry

/-- The cartesian lift of the top-open immersion into an LCI Hilbert object. -/
def lciPullbackTop_map (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    lciPullbackTop F ξ ⟶ ξ :=
  IsPreFibered.pullbackMap (p := lciP F d) rfl (topOpenHom ((lciP F d).obj ξ))

/-- The top-open lift is cartesian. -/
instance lciPullbackTop_map.isCartesian (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciP F d).IsCartesian (topOpenHom ((lciP F d).obj ξ)) (lciPullbackTop_map F ξ) :=
  IsPreFibered.pullbackMap.IsCartesian (p := lciP F d) rfl
    (topOpenHom ((lciP F d).obj ξ))

/-- The top-open lift is strongly cartesian. -/
instance lciPullbackTop_map.isStronglyCartesian (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciP F d).IsStronglyCartesian (topOpenHom ((lciP F d).obj ξ))
      (lciPullbackTop_map F ξ) :=
  IsFibered.isStronglyCartesian_of_isCartesian (lciP F d)
    (topOpenHom ((lciP F d).obj ξ)) (lciPullbackTop_map F ξ)

/-- The composite of the source top-open lift with a morphism of LCI objects lifts the
composite of the top-open immersion with the test-scheme map. -/
theorem lciPullbackTopMap_isHomLift (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    {ξ η : (lci (asGroupoidsOverMor F) d).FullSubcategory} (φ : ξ ⟶ η) :
    (lciP F d).IsHomLift (topOpenHom ((lciP F d).obj ξ) ≫ (lciP F d).map φ)
      (lciPullbackTop_map F ξ ≫ φ) :=
  sorry

/-- Top-open immersions form a naturality square with respect to morphisms of test schemes. -/
theorem lciPullbackTopMap_base (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    {ξ η : (lci (asGroupoidsOverMor F) d).FullSubcategory} (φ : ξ ⟶ η) :
    topOpenHom ((lciP F d).obj ξ) ≫ (lciP F d).map φ =
      topOpenOverMap ((lciP F d).map φ) ≫ topOpenHom ((lciP F d).obj η) :=
  sorry

/-- Functoriality of the top-open pullback of LCI Hilbert objects. -/
def lciPullbackTopMap (F : 𝒳 ⟶ 𝒴) {d : ℕ}
    {ξ η : (lci (asGroupoidsOverMor F) d).FullSubcategory} (φ : ξ ⟶ η) :
    lciPullbackTop F ξ ⟶ lciPullbackTop F η :=
  @IsStronglyCartesian.map _ _ _ _ (lciP F d)
    (topOpenOver ((lciP F d).obj η)) ((lciP F d).obj η)
    (lciPullbackTop F η) η (topOpenHom ((lciP F d).obj η)) (lciPullbackTop_map F η)
    (lciPullbackTop_map.isStronglyCartesian F η)
    (topOpenOver ((lciP F d).obj ξ)) (lciPullbackTop F ξ)
    (topOpenOverMap ((lciP F d).map φ))
    (topOpenHom ((lciP F d).obj ξ) ≫ (lciP F d).map φ) (lciPullbackTopMap_base F φ)
    (lciPullbackTop_map F ξ ≫ φ) (lciPullbackTopMap_isHomLift F φ)

/-- Transport a morphism of LCI full subcategories along an equality of degrees. -/
def lciSummandHom_eqRec (F : 𝒳 ⟶ 𝒴) {d e : ℕ} (h : d = e)
    {x y : (lci (asGroupoidsOverMor F) d).FullSubcategory} (φ : x ⟶ y) :
    Eq.mp
        (congrArg
          (fun k : ℕ ↦ (lci (asGroupoidsOverMor F) k).FullSubcategory) h)
        x ⟶
      Eq.mp
        (congrArg
          (fun k : ℕ ↦ (lci (asGroupoidsOverMor F) k).FullSubcategory) h)
        y :=
  match d, e, h with
  | _, _, rfl => φ

/-- Objects of the stack coproduct `∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴)`: a clopen partition of a
test scheme, indexed by positive degrees, together with an LCI Hilbert object on every
piece, including empty pieces. -/
structure lciCoproductObj (F : 𝒳 ⟶ 𝒴) : Type (u + 1) where
  /-- The test scheme over `S`. -/
  base : Over S
  /-- The clopen piece labelled by a positive degree. -/
  piece : lciCoproductIndex → base.left.Opens
  /-- Each piece is clopen in `base`. -/
  isClopen : ∀ i : lciCoproductIndex, IsClopen (piece i : Set base.left)
  /-- Distinct pieces are disjoint. -/
  pairwiseDisjoint :
    ∀ i j : lciCoproductIndex, i ≠ j → Disjoint (piece i : Set base.left) (piece j)
  /-- The pieces jointly cover `base`. -/
  iSup_eq_top : (⨆ i, piece i) = ⊤
  /-- An object of the corresponding LCI Hilbert stack over each piece. -/
  obj : ∀ i : lciCoproductIndex, (lci (asGroupoidsOverMor F) i.val).FullSubcategory
  /-- Each summand object lies over the corresponding piece. -/
  obj_p : ∀ i : lciCoproductIndex, (lciP F i.val).obj (obj i) =
    Over.mk ((piece i).ι ≫ base.hom)

/-- The coproduct object over `T` supported on a single positive-degree summand, with
piece `⊤` on that summand and the empty piece (carrying an explicit empty-scheme Hilbert
quintuple) on every other summand. The degree-`d` object is the cartesian pullback of `ξ`
along `topOpenHom`, so it lies strictly over `Over.mk (⊤.ι ≫ base.hom)`. -/
def lciCoproductObj.single (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    lciCoproductObj F where
  base := (lciP F d).obj ξ
  piece j := if j.val = d then ⊤ else ⊥
  isClopen := sorry
  pairwiseDisjoint := sorry
  iSup_eq_top := sorry
  obj j :=
    if h : j.val = d then
      Eq.mp
        (congrArg
          (fun k : ℕ ↦ (lci (asGroupoidsOverMor F) k).FullSubcategory) h.symm)
        (lciPullbackTop F ξ)
    else
      emptyLciObj F j.val (emptyPieceOver ((lciP F d).obj ξ))
  obj_p := sorry

/-- On the degree-`d` piece, `single` stores the top-open pullback of `ξ`. -/
theorem lciCoproductObj.single_obj_eq (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciCoproductObj.single F hd ξ).obj ⟨d, hd⟩ = lciPullbackTop F ξ :=
  sorry

/-- The test scheme of a single-summand coproduct object is the test scheme of the
inserted LCI Hilbert object. -/
theorem lciCoproductObj.single_base (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciCoproductObj.single F hd ξ).base = (lciP F d).obj ξ :=
  sorry

/-- Each piece object of a coproduct object lies in the LCI locus of its degree. -/
theorem lciCoproductObj.isLci (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F)
    (i : lciCoproductIndex) :
    Obj.IsLci (asGroupoidsOverMor F) (a.obj i).obj :=
  (a.obj i).property

/-- The open of a coproduct object corresponding to a degree, viewed as an object of
`Over S`. -/
def lciCoproductObj.pieceOver {F : 𝒳 ⟶ 𝒴} (a : lciCoproductObj F)
    (i : lciCoproductIndex) : Over S :=
  Over.mk ((a.piece i).ι ≫ a.base.hom)

/-- The piece-over object is the open subscheme of `base` corresponding to the
labelled clopen. -/
theorem lciCoproductObj.pieceOver_eq {F : 𝒳 ⟶ 𝒴} (a : lciCoproductObj F)
    (i : lciCoproductIndex) :
    a.pieceOver i = Over.mk ((a.piece i).ι ≫ a.base.hom) :=
  sorry

/-- The open-immersion of a coproduct piece into the test scheme. -/
def lciCoproductObj.pieceHom {F : 𝒳 ⟶ 𝒴} (a : lciCoproductObj F)
    (i : lciCoproductIndex) :
    a.pieceOver i ⟶ a.base :=
  Over.homMk (a.piece i).ι rfl

/-- The left map of a piece inclusion is the open immersion of that clopen. -/
theorem lciCoproductObj.pieceHom_left {F : 𝒳 ⟶ 𝒴} (a : lciCoproductObj F)
    (i : lciCoproductIndex) :
    (a.pieceHom i).left = (a.piece i).ι :=
  sorry

/-- The morphism of piece objects of `Over S` induced by a test-scheme morphism whose
preimage of each target piece is the corresponding source piece. -/
def lciCoproductHomPieceOver {F : 𝒳 ⟶ 𝒴} {a b : lciCoproductObj F}
    (base : a.base ⟶ b.base)
    (piece_pullback : ∀ i : lciCoproductIndex, a.piece i = base.left ⁻¹ᵁ b.piece i)
    (i : lciCoproductIndex) :
    a.pieceOver i ⟶ b.pieceOver i :=
  eqToHom
      (congrArg (fun U : a.base.left.Opens ↦ Over.mk (U.ι ≫ a.base.hom))
        (piece_pullback i)) ≫
    Over.homMk (base.left ∣_ b.piece i) sorry

/-- Morphisms of the stack coproduct lie over a morphism of test schemes and act
piecewise on the LCI Hilbert objects. -/
structure lciCoproductHom (F : 𝒳 ⟶ 𝒴) (a b : lciCoproductObj F) : Type u where
  /-- The underlying morphism of test schemes over `S`. -/
  base : a.base ⟶ b.base
  /-- Each source piece is the preimage of the corresponding target piece. -/
  piece_pullback : ∀ i : lciCoproductIndex, a.piece i = base.left ⁻¹ᵁ b.piece i
  /-- The piecewise morphism of LCI Hilbert objects. -/
  summand : ∀ i : lciCoproductIndex, a.obj i ⟶ b.obj i
  /-- Each summand arrow projects to the piece morphism induced by `base`. -/
  summand_over : ∀ i : lciCoproductIndex,
    (lciP F i.val).map (summand i) =
      eqToHom (a.obj_p i) ≫ lciCoproductHomPieceOver base piece_pullback i ≫
        eqToHom (b.obj_p i).symm

/-- The identity morphism of a stack-coproduct object. -/
def lciCoproductHom.id (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    lciCoproductHom F a a where
  base := 𝟙 a.base
  piece_pullback := sorry
  summand i := 𝟙 (a.obj i)
  summand_over := sorry

/-- Composition of morphisms of the stack coproduct. -/
def lciCoproductHom.comp (F : 𝒳 ⟶ 𝒴) {a b c : lciCoproductObj F}
    (f : lciCoproductHom F a b) (g : lciCoproductHom F b c) :
    lciCoproductHom F a c where
  base := f.base ≫ g.base
  piece_pullback := sorry
  summand i := f.summand i ≫ g.summand i
  summand_over := sorry

/-- The stack coproduct of positive-degree LCI Hilbert stacks, as a category. -/
instance lciCoproductObj.instCategory (F : 𝒳 ⟶ 𝒴) :
    Category.{u} (lciCoproductObj F) where
  Hom := lciCoproductHom F
  id := lciCoproductHom.id F
  comp := lciCoproductHom.comp F
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection of the stack coproduct to `Over S`. -/
def lciCoproductP (F : 𝒳 ⟶ 𝒴) : lciCoproductObj F ⥤ Over S where
  obj a := a.base
  map f := f.base
  map_id := sorry
  map_comp := sorry

/-- The object part of `lciCoproductP` is the test scheme of the clopen partition. -/
theorem lciCoproductP_obj (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    (lciCoproductP F).obj a = a.base :=
  sorry

/-- The coproduct projection is a stack in groupoids over `(Sch/S)_fppf`. -/
theorem lciCoproductP_isStack (F : 𝒳 ⟶ 𝒴) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (lciCoproductP F) :=
  sorry

/-- The coproduct stack `∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴)` over `(Sch/S)_fppf`. -/
def lciCoproduct (F : 𝒳 ⟶ 𝒴) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (lciCoproductP F)
    (lciCoproductP_isStack F)

/-- The projection of `lciCoproduct F` is the clopen-partition forgetful functor. -/
theorem lciCoproduct_p (F : 𝒳 ⟶ 𝒴) :
    (lciCoproduct F).p = lciCoproductP F :=
  sorry

/-- Inclusion of a positive-degree summand into the stack coproduct. -/
def lciCoproduct.ιFunctor (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d) :
    (lci (asGroupoidsOverMor F) d).FullSubcategory ⥤ lciCoproductObj F where
  obj ξ := lciCoproductObj.single F hd ξ
  map {x y} φ :=
    { base := (lciP F d).map φ
      piece_pullback := sorry
      summand j :=
        if h : j.val = d then
          Eq.mp
            (congrArg₂ (fun s t ↦ s ⟶ t)
              (Eq.symm (dif_pos h)) (Eq.symm (dif_pos h)))
            (lciSummandHom_eqRec F h.symm (lciPullbackTopMap F φ))
        else
          Eq.mp
            (congrArg₂ (fun s t ↦ s ⟶ t)
              (Eq.symm (dif_neg h)) (Eq.symm (dif_neg h)))
            (emptyLciMap F j.val
              (emptyOverHom
                (emptyPieceOver ((lciP F d).obj x))
                (emptyPieceOver ((lciP F d).obj y))))
      summand_over := sorry }
  map_id := sorry
  map_comp := sorry

/-- The summand inclusion lies over `(Sch/S)_fppf`. -/
theorem lciCoproduct.ι_w (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d) :
    lciCoproduct.ιFunctor F hd ⋙ (lciCoproduct F).p = (lciStack F d).p :=
  sorry

/-- The based inclusion of `H_{d,lci}(𝒳/𝒴)` into the coproduct. -/
def lciCoproduct.ιBased (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d) :
    (lciStack F d).toBasedCategory ⥤ᵇ (lciCoproduct F).toBasedCategory where
  toFunctor := lciCoproduct.ιFunctor F hd
  w := lciCoproduct.ι_w F hd

/-- The inclusion 1-morphism `H_{d,lci}(𝒳/𝒴) ⟶ ∐_{e ≥ 1} H_{e,lci}(𝒳/𝒴)`. -/
def lciCoproduct.ι (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d) :
    lciStack F d ⟶ lciCoproduct F :=
  lift (ofBasedFunctor (lciCoproduct.ιBased F hd))

/-- The object map of a summand inclusion is the single-summand coproduct object. -/
theorem lciCoproduct.ι_obj (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (lciCoproduct.ιFunctor F hd).obj ξ = lciCoproductObj.single F hd ξ :=
  sorry

/-- The image of a clopen piece under the corresponding `lciForgetToY`. -/
def lciCoproduct.forgetToYSummand (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F)
    (i : lciCoproductIndex) : 𝒴.total :=
  (toFunctor (lciForgetToY F i.val)).obj (a.obj i)

/-- The image of a clopen piece under `lciForgetToY` lies over that piece. -/
theorem lciCoproduct.forgetToYSummand_p (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F)
    (i : lciCoproductIndex) :
    𝒴.p.obj (lciCoproduct.forgetToYSummand F a i) = a.pieceOver i :=
  sorry

/-- Distinct clopen pieces of a coproduct object have empty double overlap. -/
theorem lciCoproductObj.overlap_isEmpty (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F)
    {Y₀ : Over S} {i1 i2 : lciCoproductIndex} (hne : i1 ≠ i2)
    {q : Y₀ ⟶ a.base}
    {f1 : Y₀ ⟶ a.pieceOver i1} {f2 : Y₀ ⟶ a.pieceOver i2}
    (hf1 : f1 ≫ a.pieceHom i1 = q) (hf2 : f2 ≫ a.pieceHom i2 = q) :
    IsEmpty Y₀.left :=
  sorry

/-- Descent data on the clopen pieces of a coproduct object, after applying
`lciForgetToY`. -/
def lciCoproduct.forgetToYDescentData (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    (fiberPseudofunctor 𝒴.p).DescentData a.pieceHom where
  obj i := Fiber.mk (lciCoproduct.forgetToYSummand_p F a i)
  hom Y₀ q i1 i2 f1 f2 hf1 hf2 :=
    if h : i1 = i2 then
      match i1, i2, h with
      | i0, _, rfl => eqToHom sorry
    else
      @emptyFiberHom _ _ _ 𝒴.p _ Y₀
        (lciCoproductObj.overlap_isEmpty F a h hf1 hf2)
        ((fiberPseudofunctor 𝒴.p).map f1.op.toLoc |>.toFunctor.obj
          (Fiber.mk (lciCoproduct.forgetToYSummand_p F a i1)))
        ((fiberPseudofunctor 𝒴.p).map f2.op.toLoc |>.toFunctor.obj
          (Fiber.mk (lciCoproduct.forgetToYSummand_p F a i2)))
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The clopen pieces of a coproduct object form an fppf cover of the test scheme. -/
theorem lciCoproductObj.pieceHom_mem (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    Sieve.ofArrows a.pieceOver a.pieceHom ∈
      Scheme.fppfTopology.over S a.base :=
  sorry

/-- Glue the `lciForgetToY` images of the clopen pieces of a coproduct object. -/
def lciCoproduct.toYObj (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) : 𝒴.total :=
  Fiber.fiberInclusion.obj
    (@objPreimage _ _ _ _ _
      (Pseudofunctor.isEquivalence_toDescentData
          (fiberPseudofunctor 𝒴.p) a.pieceHom
          (lciCoproductObj.pieceHom_mem F a)).essSurj
      (lciCoproduct.forgetToYDescentData F a))

/-- The glued forgetful object lies over the test scheme of the coproduct object. -/
theorem lciCoproduct.toYObj_p (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    𝒴.p.obj (lciCoproduct.toYObj F a) = a.base :=
  sorry

/-- Descent along the clopen cover of a coproduct object in `𝒴`. -/
def lciCoproduct.forgetToYDescentEquiv (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    𝒴.p.Fiber a.base ≌ (fiberPseudofunctor 𝒴.p).DescentData a.pieceHom :=
  @asEquivalence _ _ _ _
    ((fiberPseudofunctor 𝒴.p).toDescentData a.pieceHom)
    (Pseudofunctor.isEquivalence_toDescentData
      (fiberPseudofunctor 𝒴.p) a.pieceHom
      (lciCoproductObj.pieceHom_mem F a))

/-- The image of a piecewise LCI morphism under the corresponding `lciForgetToY`. -/
def lciCoproduct.forgetToYSummandHom (F : 𝒳 ⟶ 𝒴) {a b : lciCoproductObj F}
    (g : lciCoproductHom F a b) (i : lciCoproductIndex) :
    lciCoproduct.forgetToYSummand F a i ⟶ lciCoproduct.forgetToYSummand F b i :=
  (toFunctor (lciForgetToY F i.val)).map (g.summand i)

/-- The inclusion of a piecewise `lciForgetToY` image into the glued object. -/
def lciCoproduct.forgetToYSummandToGlued (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F)
    (i : lciCoproductIndex) :
    lciCoproduct.forgetToYSummand F a i ⟶ lciCoproduct.toYObj F a :=
  let xa :=
    (lciCoproduct.forgetToYDescentEquiv F a).inverse.obj
      (lciCoproduct.forgetToYDescentData F a)
  (((lciCoproduct.forgetToYDescentEquiv F a).counitIso.inv.app
        (lciCoproduct.forgetToYDescentData F a)).hom i).val ≫
    ((FiberPseudofunctor.mapIso 𝒴.p (a.pieceHom i)).hom.app xa).val ≫
    Chosen.cartesianHom 𝒴.p (a.pieceHom i) xa

/-- The cartesian reindex of a glued forgetful object along a coproduct base arrow. -/
def lciCoproduct.forgetToYPullFiber (F : 𝒳 ⟶ 𝒴) {a b : lciCoproductObj F}
    (g : lciCoproductHom F a b) : 𝒴.p.Fiber a.base :=
  Chosen.reindexObj 𝒴.p g.base (Fiber.mk (lciCoproduct.toYObj_p F b))

/-- The composite of a piecewise `lciForgetToY` image with the target inclusion lies over
the composite of the source piece inclusion with the coproduct base arrow. -/
instance lciCoproduct.forgetToYSummandToGlued_isHomLift
    {F : 𝒳 ⟶ 𝒴} {a b : lciCoproductObj F} {g : lciCoproductHom F a b}
    {i : lciCoproductIndex} :
    𝒴.p.IsHomLift (𝟙 (a.pieceOver i) ≫ a.pieceHom i ≫ g.base)
      (lciCoproduct.forgetToYSummandHom F g i ≫
        lciCoproduct.forgetToYSummandToGlued F b i) :=
  sorry

/-- The cartesian factor of a piecewise `lciForgetToY` image through the selected reindex
of the glued target. -/
def lciCoproduct.forgetToYSummandFiberHom (F : 𝒳 ⟶ 𝒴)
    {a b : lciCoproductObj F} (arr : lciCoproductHom F a b)
    (i : lciCoproductIndex) :
    lciCoproduct.forgetToYSummand F a i ⟶
      (Chosen.reindexObj 𝒴.p (a.pieceHom i ≫ arr.base)
        (Fiber.mk (lciCoproduct.toYObj_p F b))).1 :=
  @Chosen.cartesianFactor (Over S) _ 𝒴.total _ 𝒴.p _
    b.base (a.pieceOver i) (a.pieceOver i)
    (a.pieceHom i ≫ arr.base) (𝟙 (a.pieceOver i))
    (Fiber.mk (lciCoproduct.toYObj_p F b))
    (lciCoproduct.forgetToYSummand F a i)
    (lciCoproduct.forgetToYSummandHom F arr i ≫
      lciCoproduct.forgetToYSummandToGlued F b i)
    lciCoproduct.forgetToYSummandToGlued_isHomLift

/-- The descent-datum morphism over the source clopen cover whose components are the
cartesian factors of the piecewise `lciForgetToY` images. -/
def lciCoproduct.forgetToYDescentHom (F : 𝒳 ⟶ 𝒴) {a b : lciCoproductObj F}
    (g : lciCoproductHom F a b) :
    lciCoproduct.forgetToYDescentData F a ⟶
      ((fiberPseudofunctor 𝒴.p).toDescentData a.pieceHom).obj
        (lciCoproduct.forgetToYPullFiber F g) where
  hom i :=
    ⟨lciCoproduct.forgetToYSummandFiberHom F g i ≫
        (Chosen.Reindex.specifiedCompIsoApp 𝒴.p g.base (a.pieceHom i)
          (a.pieceHom i ≫ g.base) rfl
          (Fiber.mk (lciCoproduct.toYObj_p F b))).hom.1 ≫
        Fiber.fiberInclusion.map
          ((FiberPseudofunctor.mapIso 𝒴.p (a.pieceHom i)).inv.app
            (lciCoproduct.forgetToYPullFiber F g)),
      sorry⟩
  comm := sorry

/-- The fold arrow of `lciForgetToY` images, obtained as the image of
`forgetToYDescentHom` under descent along the source clopen cover. -/
def lciCoproduct.toYMap (F : 𝒳 ⟶ 𝒴) {a b : lciCoproductObj F}
    (g : lciCoproductHom F a b) :
    lciCoproduct.toYObj F a ⟶ lciCoproduct.toYObj F b :=
  Fiber.fiberInclusion.map
      ((lciCoproduct.forgetToYDescentEquiv F a).inverse.map
          (lciCoproduct.forgetToYDescentHom F g) ≫
        (lciCoproduct.forgetToYDescentEquiv F a).unitIso.inv.app
          (lciCoproduct.forgetToYPullFiber F g)) ≫
    Chosen.cartesianHom 𝒴.p g.base (Fiber.mk (lciCoproduct.toYObj_p F b))

/-- The total functor of `∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴) ⟶ 𝒴`, obtained by gluing
`lciForgetToY` along clopen covers. -/
def lciCoproduct.toYFunctor (F : 𝒳 ⟶ 𝒴) : lciCoproductObj F ⥤ 𝒴.total where
  obj := lciCoproduct.toYObj F
  map := lciCoproduct.toYMap F
  map_id := sorry
  map_comp := sorry

/-- The coproduct forgetful functor lies over `(Sch/S)_fppf`. -/
theorem lciCoproduct.toY_w (F : 𝒳 ⟶ 𝒴) :
    lciCoproduct.toYFunctor F ⋙ 𝒴.p = (lciCoproduct F).p :=
  sorry

/-- The based forgetful functor of the LCI Hilbert coproduct. -/
def lciCoproduct.toYBased (F : 𝒳 ⟶ 𝒴) :
    (lciCoproduct F).toBasedCategory ⥤ᵇ 𝒴.toBasedCategory where
  toFunctor := lciCoproduct.toYFunctor F
  w := lciCoproduct.toY_w F

/-- The forgetful 1-morphism `∐_{d ≥ 1} H_{d,lci}(𝒳/𝒴) ⟶ 𝒴`. -/
def lciCoproduct.forgetToY (F : 𝒳 ⟶ 𝒴) : lciCoproduct F ⟶ 𝒴 :=
  lift (ofBasedFunctor (lciCoproduct.toYBased F))

/-- The object map of the coproduct forgetful functor is the glued `lciForgetToY`
image of the clopen pieces. -/
theorem lciCoproduct.forgetToY_obj (F : 𝒳 ⟶ 𝒴) (a : lciCoproductObj F) :
    (lciCoproduct.toYFunctor F).obj a = lciCoproduct.toYObj F a :=
  sorry

/-- The degree-`d` summand image under `lciForgetToY` is the top-open pullback image. -/
def lciCoproduct.forgetToY_comp_ι_summandIso (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    lciCoproduct.forgetToYSummand F (lciCoproductObj.single F hd ξ) ⟨d, hd⟩ ≅
      (toFunctor (lciForgetToY F d)).obj (lciPullbackTop F ξ) :=
  eqToIso
    (congrArg (toFunctor (lciForgetToY F d)).obj
      (lciCoproductObj.single_obj_eq F hd ξ))

/-- The comparison from the top-open pullback image to the glued coproduct forgetful
object is co-cartesian over the top-open immersion. -/
theorem lciCoproduct.forgetToY_comp_ι_glued_isCocartesian
    (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    IsCocartesian 𝒴.p (topOpenHom ((lciP F d).obj ξ))
      ((lciCoproduct.forgetToY_comp_ι_summandIso F hd ξ).inv ≫
        lciCoproduct.forgetToYSummandToGlued F (lciCoproductObj.single F hd ξ)
          ⟨d, hd⟩) :=
  sorry

/-- The image of the top-open cartesian lift under `lciForgetToY` is co-cartesian over
the top-open immersion. -/
theorem lciCoproduct.forgetToY_comp_ι_orig_isCocartesian
    (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    IsCocartesian 𝒴.p (topOpenHom ((lciP F d).obj ξ))
      ((toFunctor (lciForgetToY F d)).map (lciPullbackTop_map F ξ)) :=
  sorry

/-- Objectwise comparison: gluing along the clopen cover `{⊤} ∪ {⊥}` recovers
`lciForgetToY` up to the cartesian top-open round-trip, not definitionally. -/
def lciCoproduct.forgetToY_comp_ι_objIso (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    lciCoproduct.toYObj F (lciCoproductObj.single F hd ξ) ≅
      (toFunctor (lciForgetToY F d)).obj ξ :=
  @IsCocartesian.codomainUniqueUpToIso _ _ _ _ 𝒴.p
    (topOpenOver ((lciP F d).obj ξ)) ((lciP F d).obj ξ)
    ((toFunctor (lciForgetToY F d)).obj (lciPullbackTop F ξ))
    (lciCoproduct.toYObj F (lciCoproductObj.single F hd ξ))
    (topOpenHom ((lciP F d).obj ξ))
    ((lciCoproduct.forgetToY_comp_ι_summandIso F hd ξ).inv ≫
      lciCoproduct.forgetToYSummandToGlued F (lciCoproductObj.single F hd ξ)
        ⟨d, hd⟩)
    (lciCoproduct.forgetToY_comp_ι_glued_isCocartesian F hd ξ)
    ((toFunctor (lciForgetToY F d)).obj ξ)
    ((toFunctor (lciForgetToY F d)).map (lciPullbackTop_map F ξ))
    (lciCoproduct.forgetToY_comp_ι_orig_isCocartesian F hd ξ)

/-- The total functor of `ι ≫ lciCoproduct.forgetToY` sends `ξ` to the glued object of
`single ξ`. -/
theorem lciCoproduct.toFunctor_ι_comp_forgetToY_obj (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (toFunctor (lciCoproduct.ι F hd ≫ lciCoproduct.forgetToY F)).obj ξ =
      lciCoproduct.toYObj F (lciCoproductObj.single F hd ξ) :=
  sorry

/-- Objectwise 2-cell of `ι ≫ lciCoproduct.forgetToY ≅ lciForgetToY`. -/
def lciCoproduct.forgetToY_comp_ι_app (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    (toFunctor (lciCoproduct.ι F hd ≫ lciCoproduct.forgetToY F)).obj ξ ≅
      (toFunctor (lciForgetToY F d)).obj ξ :=
  eqToIso (lciCoproduct.toFunctor_ι_comp_forgetToY_obj F hd ξ) ≪≫
    lciCoproduct.forgetToY_comp_ι_objIso F hd ξ

/-- Naturality of the objectwise comparison `ι ≫ lciCoproduct.forgetToY ≅ lciForgetToY`. -/
theorem lciCoproduct.forgetToY_comp_ι_naturality (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    {ξ η : (lci (asGroupoidsOverMor F) d).FullSubcategory} (φ : ξ ⟶ η) :
    (toFunctor (lciCoproduct.ι F hd ≫ lciCoproduct.forgetToY F)).map φ ≫
        (lciCoproduct.forgetToY_comp_ι_app F hd η).hom =
      (lciCoproduct.forgetToY_comp_ι_app F hd ξ).hom ≫
        (toFunctor (lciForgetToY F d)).map φ :=
  sorry

/-- The objectwise comparison is vertical over the identity of the test scheme. -/
theorem lciCoproduct.forgetToY_comp_ι_isHomLift (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d)
    (ξ : (lci (asGroupoidsOverMor F) d).FullSubcategory) :
    𝒴.p.IsHomLift (𝟙 ((lciP F d).obj ξ))
      (lciCoproduct.forgetToY_comp_ι_app F hd ξ).hom :=
  sorry

/-- On the degree-`d` summand, the coproduct forgetful map is 2-isomorphic to
`lciForgetToY`, since gluing is a descent preimage and the top-open round-trip is
cartesian rather than definitional. -/
def lciCoproduct.forgetToY_comp_ι (F : 𝒳 ⟶ 𝒴) {d : ℕ} (hd : 0 < d) :
    lciCoproduct.ι F hd ≫ lciCoproduct.forgetToY F ≅ lciForgetToY F d :=
  isoMk
    (BasedFunctorIso.lift
      (BasedNatIso.ofComponents
        (fun ξ ↦ lciCoproduct.forgetToY_comp_ι_app F hd ξ)
        (fun φ ↦ lciCoproduct.forgetToY_comp_ι_naturality F hd φ)
        (fun ξ ↦ lciCoproduct.forgetToY_comp_ι_isHomLift F hd ξ)))

end AlgebraicGeometry.FiniteHilbertStack
