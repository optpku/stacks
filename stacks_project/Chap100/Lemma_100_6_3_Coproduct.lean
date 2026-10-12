/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.Clopen
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Finite coproducts of groupoid fibrations as stacks

The finite disjoint union of algebraic stacks over `Over S` is the stack
coproduct of the summands: an object over a test scheme `T` is a pairwise
disjoint, jointly covering family of clopen pieces of `T`, indexed by the
`u`-small model of the finite index type (including empty pieces), together
with an object of the corresponding summand over each piece. Morphisms lie
over a morphism of test schemes and act piecewise on the summand objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The empty open subscheme of a scheme is an empty scheme. -/
instance {X : Scheme.{u}} : IsEmpty (⊥ : X.Opens).toScheme :=
  inferInstanceAs (IsEmpty (∅ : Set X))

/-- The empty open of a test scheme over `S` is an empty object of `Over S`. -/
instance {S : Scheme.{u}} (T : Over S) :
    IsEmpty (Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom)).left :=
  inferInstanceAs (IsEmpty (⊥ : T.left.Opens).toScheme)

end AlgebraicGeometry

namespace AlgebraicGeometry.GroupoidsOver

/-- A `u`-small model of a finite index type. -/
abbrev coproductIndex (I : Type v) [Finite I] : Type u :=
  ULift.{u, 0} (Fin (@Fintype.card I (Fintype.ofFinite I)))

/-- Identification of a finite index type with its `u`-small model. -/
def coproductIndexEquiv (I : Type v) [Finite I] : I ≃ coproductIndex.{u} I :=
  (@Fintype.equivFin I (Fintype.ofFinite I)).trans (Equiv.ulift.{u, 0}).symm

/-- The atlas scheme of an algebraic stack, chosen from the smooth surjective atlas. -/
def atlasOver {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Over S :=
  Exists.choose (AlgebraicStack.existsSmoothSurjectiveAtlas (X := X))

/-- The atlas 1-morphism of an algebraic stack, chosen from the smooth surjective atlas. -/
def atlasHom {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    GroupoidsOver.slice (atlasOver X) ⟶ X :=
  Exists.choose (Exists.choose_spec (AlgebraicStack.existsSmoothSurjectiveAtlas (X := X)))

/-- The image of the identity object of the atlas slice under the atlas 1-morphism. -/
def atlasObj {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : X.total :=
  (FiberedCategoryOver.Groupoids.toFunctor (atlasHom X)).obj (Over.mk (𝟙 (atlasOver X)))

/-- The unique morphism in `Over S` out of an empty test scheme. -/
def emptyOverHom {S : Scheme.{u}} (T U : Over S) [IsEmpty T.left] : T ⟶ U :=
  Over.homMk (isInitialOfIsEmpty.to U.left)
    (isInitialOfIsEmpty.hom_ext (isInitialOfIsEmpty.to U.left ≫ U.hom) T.hom)

/-- An object of an algebraic stack over an empty test scheme, obtained by cartesian
pullback of the atlas object along the unique map from the empty scheme. -/
def emptyObj {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (T : Over S) [IsEmpty T.left] : X.total :=
  IsPreFibered.pullbackObj (p := X.p) rfl (emptyOverHom T (X.p.obj (atlasObj X)))

/-- The cartesian arrow from `emptyObj X T` to the atlas object. -/
def emptyObj_toAtlas {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (T : Over S) [IsEmpty T.left] :
    emptyObj X T ⟶ atlasObj X :=
  IsPreFibered.pullbackMap (p := X.p) rfl (emptyOverHom T (X.p.obj (atlasObj X)))

/-- The projection of an algebraic stack is fibered, so cartesian atlas pullbacks are
strongly cartesian. -/
instance instIsFibered_p {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    X.p.IsFibered :=
  (inferInstance : Functor.IsFibered.InGroupoids X.p).toIsFibered

/-- The atlas pullback of an empty test scheme is cartesian. -/
instance emptyObj_toAtlas.isCartesian {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (T : Over S) [IsEmpty T.left] :
    X.p.IsCartesian (emptyOverHom T (X.p.obj (atlasObj X))) (emptyObj_toAtlas X T) :=
  IsPreFibered.pullbackMap.IsCartesian (p := X.p) rfl
    (emptyOverHom T (X.p.obj (atlasObj X)))

/-- The atlas pullback of an empty test scheme is strongly cartesian. -/
instance emptyObj_toAtlas.isStronglyCartesian {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (T : Over S) [IsEmpty T.left] :
    X.p.IsStronglyCartesian (emptyOverHom T (X.p.obj (atlasObj X)))
      (emptyObj_toAtlas X T) :=
  IsFibered.isStronglyCartesian_of_isCartesian X.p
    (emptyOverHom T (X.p.obj (atlasObj X))) (emptyObj_toAtlas X T)

/-- Functoriality of `emptyObj` along a morphism of empty test schemes, induced by the
universal property of the cartesian atlas pullback. -/
def emptyObj_map {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    {T T' : Over S} [IsEmpty T.left] [IsEmpty T'.left] (f : T ⟶ T') :
    emptyObj X T ⟶ emptyObj X T' :=
  IsStronglyCartesian.map (p := X.p)
    (emptyOverHom T' (X.p.obj (atlasObj X))) (emptyObj_toAtlas X T')
    (Over.OverMorphism.ext
      (isInitialOfIsEmpty.hom_ext
        (emptyOverHom T (X.p.obj (atlasObj X))).left
        (f ≫ emptyOverHom T' (X.p.obj (atlasObj X))).left))
    (emptyObj_toAtlas X T)

/-- Transport a morphism of summand total categories along an equality of indices. -/
def coproductSummandHom_eqRec {S : Scheme.{u}} {I : Type v}
    (X : I → GroupoidsOver S) {i j : I} (h : i = j) {x y : (X i).total}
    (φ : x ⟶ y) :
    Eq.mp (congrArg (fun k : I ↦ (X k).total) h) x ⟶
      Eq.mp (congrArg (fun k : I ↦ (X k).total) h) y :=
  match i, j, h with
  | _, _, rfl => φ

/-- Objects of the stack coproduct of a finite family of groupoid fibrations over
`Over S`: a clopen partition of a test scheme together with a summand object on
every piece, including empty pieces. -/
structure coproductTotal {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) : Type (u + 1) where
  /-- The test scheme over `S`. -/
  base : Over S
  /-- The clopen piece of `base` labelled by an index in the `u`-small model. -/
  piece : coproductIndex.{u} I → base.left.Opens
  /-- Each piece is clopen in `base`. -/
  isClopen : ∀ i, IsClopen (piece i : Set base.left)
  /-- Distinct pieces are disjoint. -/
  pairwiseDisjoint :
    ∀ i j, i ≠ j → Disjoint (piece i : Set base.left) (piece j)
  /-- The pieces jointly cover `base`. -/
  iSup_eq_top : (⨆ i, piece i) = ⊤
  /-- An object of the corresponding summand over each piece, including empty pieces. -/
  obj : ∀ i, (X ((coproductIndexEquiv.{u} I).symm i)).total
  /-- Each summand object lies over the corresponding piece. -/
  obj_p : ∀ i,
    (X ((coproductIndexEquiv.{u} I).symm i)).p.obj (obj i) =
      Over.mk ((piece i).ι ≫ base.hom)

/-- The empty piece of a test scheme, as an object of `Over S`. -/
abbrev emptyPieceOver {S : Scheme.{u}} (T : Over S) : Over S :=
  Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom)

/-- The coproduct object over `T` supported on a single summand `i`, with piece `⊤` on
that summand and the empty piece (carrying the atlas pullback) on every other summand. -/
def coproductTotal.single {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] (i : I)
    (x : (X i).total) : coproductTotal X where
  base := (X i).p.obj x
  piece j := if j = coproductIndexEquiv.{u} I i then ⊤ else ⊥
  isClopen := sorry
  pairwiseDisjoint := sorry
  iSup_eq_top := sorry
  obj j :=
    if h : j = coproductIndexEquiv.{u} I i then
      Eq.mp
        (congrArg (fun k : I ↦ (X k).total)
          (Eq.trans (congrArg (coproductIndexEquiv.{u} I).symm h)
            ((coproductIndexEquiv.{u} I).symm_apply_apply i)).symm)
        x
    else
      emptyObj (X ((coproductIndexEquiv.{u} I).symm j))
        (emptyPieceOver ((X i).p.obj x))
  obj_p := sorry

/-- The open of a coproduct object corresponding to an index, viewed as an object of
`Over S`. -/
def coproductTotal.pieceOver {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (a : coproductTotal X) (i : coproductIndex.{u} I) :
    Over S :=
  Over.mk ((a.piece i).ι ≫ a.base.hom)

/-- The open-immersion of a coproduct piece into the test scheme. -/
def coproductTotal.pieceHom {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (a : coproductTotal X) (i : coproductIndex.{u} I) :
    a.pieceOver i ⟶ a.base :=
  Over.homMk (a.piece i).ι rfl

/-- The morphism of piece objects of `Over S` induced by a test-scheme morphism whose
preimage of each target piece is the corresponding source piece. -/
def coproductHomPieceOver {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {a b : coproductTotal X}
    (base : a.base ⟶ b.base)
    (piece_pullback : ∀ i, a.piece i = base.left ⁻¹ᵁ b.piece i)
    (i : coproductIndex.{u} I) :
    a.pieceOver i ⟶ b.pieceOver i :=
  eqToHom
      (congrArg (fun U : a.base.left.Opens ↦ Over.mk (U.ι ≫ a.base.hom))
        (piece_pullback i)) ≫
    Over.homMk (base.left ∣_ b.piece i) sorry

/-- Morphisms of the stack coproduct lie over a morphism of test schemes and act
piecewise on the summand objects. -/
structure coproductHom {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (a b : coproductTotal X) : Type u where
  /-- The underlying morphism of test schemes over `S`. -/
  base : a.base ⟶ b.base
  /-- Each source piece is the preimage of the corresponding target piece. -/
  piece_pullback : ∀ i, a.piece i = base.left ⁻¹ᵁ b.piece i
  /-- The piecewise morphism of summand objects. -/
  summand :
    ∀ i, a.obj i ⟶ b.obj i
  /-- Each summand arrow projects to the piece morphism induced by `base` and
  `piece_pullback`, after transporting along `obj_p`. -/
  summand_over : ∀ i,
    (X ((coproductIndexEquiv.{u} I).symm i)).p.map (summand i) =
      eqToHom (a.obj_p i) ≫ coproductHomPieceOver base piece_pullback i ≫
        eqToHom (b.obj_p i).symm

/-- The identity morphism of a stack-coproduct object. -/
def coproductHom.id {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (a : coproductTotal X) : coproductHom a a where
  base := 𝟙 a.base
  piece_pullback := sorry
  summand i := 𝟙 (a.obj i)
  summand_over := sorry

/-- Composition of morphisms of the stack coproduct. -/
def coproductHom.comp {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {a b c : coproductTotal X}
    (f : coproductHom a b) (g : coproductHom b c) : coproductHom a c where
  base := f.base ≫ g.base
  piece_pullback := sorry
  summand i := f.summand i ≫ g.summand i
  summand_over := sorry

/-- The morphism of piece objects of `Over S` induced by a coproduct arrow. -/
def coproductHom.pieceOverHom {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {a b : coproductTotal X} (g : coproductHom a b)
    (i : coproductIndex.{u} I) :
    a.pieceOver i ⟶ b.pieceOver i :=
  coproductHomPieceOver g.base g.piece_pullback i

/-- The stack coproduct of a finite family of groupoid fibrations, as a category. -/
instance instCategoryCoproductTotal {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) : Category.{u} (coproductTotal X) where
  Hom := coproductHom
  id := coproductHom.id
  comp := coproductHom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Inclusion of a summand object into the stack coproduct. -/
def coproductιFunctor {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] (i : I) :
    (X i).total ⥤ coproductTotal X where
  obj x := coproductTotal.single X i x
  map {x y} φ :=
    { base := (X i).p.map φ
      piece_pullback := sorry
      summand j :=
        if h : j = coproductIndexEquiv.{u} I i then
          Eq.mp
            (congrArg₂ (fun s t ↦ s ⟶ t)
              (Eq.symm
                (dif_pos h :
                  (coproductTotal.single X i x).obj j =
                    Eq.mp
                      (congrArg (fun k : I ↦ (X k).total)
                        (Eq.trans (congrArg (coproductIndexEquiv.{u} I).symm h)
                          ((coproductIndexEquiv.{u} I).symm_apply_apply i)).symm)
                      x))
              (Eq.symm
                (dif_pos h :
                  (coproductTotal.single X i y).obj j =
                    Eq.mp
                      (congrArg (fun k : I ↦ (X k).total)
                        (Eq.trans (congrArg (coproductIndexEquiv.{u} I).symm h)
                          ((coproductIndexEquiv.{u} I).symm_apply_apply i)).symm)
                      y)))
            (coproductSummandHom_eqRec X
              (Eq.trans (congrArg (coproductIndexEquiv.{u} I).symm h)
                ((coproductIndexEquiv.{u} I).symm_apply_apply i)).symm
              φ)
        else
          Eq.mp
            (congrArg₂ (fun s t ↦ s ⟶ t) (Eq.symm (dif_neg h)) (Eq.symm (dif_neg h)))
            (emptyObj_map (X ((coproductIndexEquiv.{u} I).symm j))
              (emptyOverHom
                (emptyPieceOver ((X i).p.obj x))
                (emptyPieceOver ((X i).p.obj y))))
      summand_over := sorry }
  map_id := sorry
  map_comp := sorry

/-- The projection of the stack coproduct to `Over S`. -/
def coproductFunctor {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) : coproductTotal X ⥤ Over S where
  obj a := a.base
  map f := f.base
  map_id := sorry
  map_comp := sorry

/-- The stack-coproduct projection is fibred in groupoids. -/
instance instIsFiberedInGroupoids_coproductFunctor {S : Scheme.{u}} {I : Type v}
    [Finite I] (X : I → GroupoidsOver S) :
    Functor.IsFibered.InGroupoids (coproductFunctor X) :=
  sorry

/-- The finite stack coproduct of categories fibred in groupoids over `Over S`. -/
def coproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor (coproductFunctor X)

/-- The projection of the finite stack coproduct is the clopen-partition projection. -/
theorem coproduct_p {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) : (coproduct X).p = coproductFunctor X :=
  sorry

/-- The based functor underlying the inclusion of a summand. -/
def coproductιBased {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] (i : I) :
    BasedFunctor (X i).toBasedCategory (coproduct X).toBasedCategory where
  toFunctor := coproductιFunctor X i
  w := sorry

/-- The canonical inclusion of a summand into the finite stack coproduct. -/
def coproductι {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] (i : I) :
    X i ⟶ coproduct X :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (coproductιBased X i)

/-- The image of a summand object under a family of 1-morphisms. -/
def coproductDesc_summandObj {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} (f : ∀ i, X i ⟶ Y)
    (a : coproductTotal X) (i : coproductIndex.{u} I) : Y.total :=
  (FiberedCategoryOver.Groupoids.toFunctor
      (f ((coproductIndexEquiv.{u} I).symm i))).obj (a.obj i)

/-- The image of a summand object lies over the corresponding piece. -/
theorem coproductDesc_summandObj_p {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} (f : ∀ i, X i ⟶ Y)
    (a : coproductTotal X) (i : coproductIndex.{u} I) :
    Y.p.obj (coproductDesc_summandObj f a i) = a.pieceOver i :=
  sorry

/-- The empty covering family of objects of `Over S`. -/
def emptyCoverObjs {S : Scheme.{u}} : PEmpty.{u + 1} → Over S :=
  fun i ↦ nomatch i

/-- The empty covering family of arrows into a test scheme. -/
def emptyCoverHoms {S : Scheme.{u}} (T : Over S) :
    ∀ i : PEmpty.{u + 1}, emptyCoverObjs i ⟶ T :=
  fun i ↦ nomatch i

/-- The empty family of arrows covers an empty test scheme in the big fppf topology. -/
theorem emptyArrows_cover_mem {S : Scheme.{u}} (T : Over S) [IsEmpty T.left] :
    Sieve.ofArrows emptyCoverObjs (emptyCoverHoms T) ∈
      Scheme.fppfTopology.over S T :=
  Eq.mp
    (congrArg (fun s : Sieve T ↦ s ∈ Scheme.fppfTopology.over S T)
      (Eq.symm
        (Eq.trans
          (congrArg Sieve.generate (Presieve.ofArrows_of_isEmpty (emptyCoverHoms T)))
          Sieve.generate_bot)))
    ((Scheme.fppfTopology.mem_over_iff (⊥ : Sieve T)).mpr
      ((Sieve.overEquiv T).map_bot.symm ▸
        Scheme.bot_mem_grothendieckTopology T.left))

/-- The unique morphism between descent data for an empty covering family. -/
def emptyDescentHom {S : Scheme.{u}} (Y : GroupoidsOver S) (T : Over S)
    (D₁ D₂ : (Functor.fiberPseudofunctor Y.p).DescentData (emptyCoverHoms T)) :
    D₁ ⟶ D₂ where
  hom i := nomatch i

/-- A morphism in the fibre over an empty test scheme, obtained by fully faithful descent
along the empty cover. -/
def emptyFiberHom {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y]
    (T : Over S) (hT : IsEmpty T.left) (x z : Y.p.Fiber T) : x ⟶ z :=
  let F := (Functor.fiberPseudofunctor Y.p).toDescentData (emptyCoverHoms T)
  let hEq : F.IsEquivalence :=
    Pseudofunctor.isEquivalence_toDescentData
      (Functor.fiberPseudofunctor Y.p) (emptyCoverHoms T)
      (@emptyArrows_cover_mem S T hT)
  (@Functor.FullyFaithful.ofFullyFaithful _ _ _ _ F hEq.full hEq.faithful).preimage
    (emptyDescentHom Y T (F.obj x) (F.obj z))

/-- Distinct clopen pieces of a coproduct object have empty double overlap. -/
theorem coproductTotal.overlap_isEmpty {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (a : coproductTotal X)
    {Y₀ : Over S} {i1 i2 : coproductIndex.{u} I} (hne : i1 ≠ i2)
    {q : Y₀ ⟶ a.base}
    {f1 : Y₀ ⟶ a.pieceOver i1} {f2 : Y₀ ⟶ a.pieceOver i2}
    (hf1 : f1 ≫ a.pieceHom i1 = q) (hf2 : f2 ≫ a.pieceHom i2 = q) :
    IsEmpty Y₀.left :=
  sorry

/-- Descent data on the clopen pieces of a coproduct object, after applying a family
of 1-morphisms. -/
def coproductDesc_descentData {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) (a : coproductTotal X) :
    (Functor.fiberPseudofunctor Y.p).DescentData a.pieceHom where
  obj i := Fiber.mk (coproductDesc_summandObj_p f a i)
  hom Y₀ q i1 i2 f1 f2 hf1 hf2 :=
    if h : i1 = i2 then
      match i1, i2, h with
      | i0, _, rfl =>
        eqToHom
          (congrArg
            (fun g : Y₀ ⟶ a.pieceOver i0 ↦
              ((Functor.fiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.obj
                (Fiber.mk (coproductDesc_summandObj_p f a i0)))
            (Over.OverMorphism.ext
              ((cancel_mono (a.piece i0).ι).1
                ((congrArg CommaMorphism.left hf1).trans
                  (congrArg CommaMorphism.left hf2).symm))))
    else
      emptyFiberHom Y Y₀ (coproductTotal.overlap_isEmpty a h hf1 hf2)
        ((Functor.fiberPseudofunctor Y.p).map f1.op.toLoc |>.toFunctor.obj
          (Fiber.mk (coproductDesc_summandObj_p f a i1)))
        ((Functor.fiberPseudofunctor Y.p).map f2.op.toLoc |>.toFunctor.obj
          (Fiber.mk (coproductDesc_summandObj_p f a i2)))
  pullHom_hom := sorry
  hom_self := sorry
  hom_comp := sorry

/-- The clopen pieces of a coproduct object form an fppf cover of the test scheme. -/
theorem coproductTotal.pieceHom_mem {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (a : coproductTotal X) :
    Sieve.ofArrows a.pieceOver a.pieceHom ∈ Scheme.fppfTopology.over S a.base :=
  sorry

/-- Glue the images of the clopen pieces of a coproduct object under a family of
1-morphisms, using effectiveness of descent in the target stack. -/
def coproductDescObj {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) (a : coproductTotal X) : Y.total :=
  Fiber.fiberInclusion.obj
    (@Functor.objPreimage _ _ _ _ _
      (Pseudofunctor.isEquivalence_toDescentData
          (Functor.fiberPseudofunctor Y.p) a.pieceHom a.pieceHom_mem).essSurj
      (coproductDesc_descentData f a))

/-- The image of a piecewise summand morphism under a family of 1-morphisms. -/
def coproductDesc_summandHom {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} (f : ∀ i, X i ⟶ Y)
    {a b : coproductTotal X} (g : coproductHom a b) (i : coproductIndex.{u} I) :
    coproductDesc_summandObj f a i ⟶ coproductDesc_summandObj f b i :=
  (FiberedCategoryOver.Groupoids.toFunctor
      (f ((coproductIndexEquiv.{u} I).symm i))).map (g.summand i)

/-- The glued fold object lies over the test scheme of the coproduct object. -/
theorem coproductDescObj_p {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) (a : coproductTotal X) :
    Y.p.obj (coproductDescObj f a) = a.base :=
  sorry

/-- Descent along the clopen cover of a coproduct object in a target algebraic stack. -/
def coproductDesc_descentEquiv {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} (Y : GroupoidsOver S) [AlgebraicStack Y]
    (a : coproductTotal X) :
    Y.p.Fiber a.base ≌ (Functor.fiberPseudofunctor Y.p).DescentData a.pieceHom :=
  @Functor.asEquivalence _ _ _ _
    ((Functor.fiberPseudofunctor Y.p).toDescentData a.pieceHom)
    (Pseudofunctor.isEquivalence_toDescentData
      (Functor.fiberPseudofunctor Y.p) a.pieceHom a.pieceHom_mem)

/-- The inclusion of a piecewise summand image into the glued fold object, obtained from
the counit of descent along the clopen cover. -/
def coproductDesc_summandToGlued {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) (a : coproductTotal X) (i : coproductIndex.{u} I) :
    coproductDesc_summandObj f a i ⟶ coproductDescObj f a :=
  let xa := (coproductDesc_descentEquiv Y a).inverse.obj (coproductDesc_descentData f a)
  Fiber.fiberInclusion.map
      (((coproductDesc_descentEquiv Y a).counitIso.inv.app
        (coproductDesc_descentData f a)).hom i) ≫
    Fiber.fiberInclusion.map
      ((FiberPseudofunctor.mapIso Y.p (a.pieceHom i)).hom.app xa) ≫
    Chosen.cartesianHom Y.p (a.pieceHom i) xa

/-- The cartesian reindex of a glued fold object along a coproduct base arrow. -/
def coproductDesc_pullFiber {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) {a b : coproductTotal X} (g : coproductHom a b) :
    Y.p.Fiber a.base :=
  Chosen.reindexObj Y.p g.base (Fiber.mk (coproductDescObj_p f b))

/-- The composite of a piecewise summand image with the target inclusion lies over the
composite of the source piece inclusion with the coproduct base arrow. -/
instance coproductDesc_summandToGlued_isHomLift
    {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    {f : ∀ i, X i ⟶ Y} {a b : coproductTotal X} {g : coproductHom a b}
    {i : coproductIndex.{u} I} :
    (FiberedCategoryOver.Groupoids.p Y).IsHomLift
      (𝟙 (a.pieceOver i) ≫ a.pieceHom i ≫ g.base)
      (coproductDesc_summandHom f g i ≫ coproductDesc_summandToGlued f b i) :=
  sorry

/-- The cartesian factor of a piecewise summand image through the selected reindex of
the glued target along the source piece inclusion followed by the coproduct base. -/
def coproductDesc_summandFiberHom {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (fam : ∀ i, X i ⟶ Y) {a b : coproductTotal X} (arr : coproductHom a b)
    (i : coproductIndex.{u} I) :
    coproductDesc_summandObj fam a i ⟶
      (Chosen.reindexObj Y.p (a.pieceHom i ≫ arr.base)
        (Fiber.mk (coproductDescObj_p fam b))).1 :=
  @Chosen.cartesianFactor (Over S) _ Y.total _ Y.p _
    b.base (a.pieceOver i) (a.pieceOver i)
    (a.pieceHom i ≫ arr.base) (𝟙 (a.pieceOver i))
    (Fiber.mk (coproductDescObj_p fam b))
    (coproductDesc_summandObj fam a i)
    (coproductDesc_summandHom fam arr i ≫ coproductDesc_summandToGlued fam b i)
    coproductDesc_summandToGlued_isHomLift

/-- The descent-datum morphism over the source clopen cover whose components are the
cartesian factors of `coproductDesc_summandHom`. -/
def coproductDesc_descentHom {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) {a b : coproductTotal X} (g : coproductHom a b) :
    coproductDesc_descentData f a ⟶
      ((Functor.fiberPseudofunctor Y.p).toDescentData a.pieceHom).obj
        (coproductDesc_pullFiber f g) where
  hom i :=
    ⟨coproductDesc_summandFiberHom f g i ≫
        (Chosen.Reindex.specifiedCompIsoApp Y.p g.base (a.pieceHom i)
          (a.pieceHom i ≫ g.base) rfl
          (Fiber.mk (coproductDescObj_p f b))).hom.1 ≫
        Fiber.fiberInclusion.map
          ((FiberPseudofunctor.mapIso Y.p (a.pieceHom i)).inv.app
            (coproductDesc_pullFiber f g)),
      sorry⟩
  comm := sorry

/-- The fold arrow of a family of 1-morphisms, obtained as the image of
`coproductDesc_descentHom` under descent along the source clopen cover. -/
def coproductDesc_map {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) {a b : coproductTotal X} (g : coproductHom a b) :
    coproductDescObj f a ⟶ coproductDescObj f b :=
  Fiber.fiberInclusion.map
      ((coproductDesc_descentEquiv Y a).inverse.map (coproductDesc_descentHom f g) ≫
        (coproductDesc_descentEquiv Y a).unitIso.inv.app (coproductDesc_pullFiber f g)) ≫
    Chosen.cartesianHom Y.p g.base (Fiber.mk (coproductDescObj_p f b))

/-- The fold functor on total categories induced by a family of 1-morphisms, obtained
by gluing the images of the clopen pieces. -/
def coproductDescFunctor {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) : coproductTotal X ⥤ Y.total where
  obj a := coproductDescObj f a
  map g := coproductDesc_map f g
  map_id := sorry
  map_comp := sorry

/-- The based functor underlying the coproduct fold of a family of 1-morphisms. -/
def coproductDescBased {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) :
    BasedFunctor (coproduct X).toBasedCategory Y.toBasedCategory where
  toFunctor := coproductDescFunctor f
  w := sorry

/-- The 1-morphism out of the finite stack coproduct induced by a family of
1-morphisms from the summands, obtained by gluing along clopen pieces. -/
def coproductDesc {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [AlgebraicStack Y]
    (f : ∀ i, X i ⟶ Y) : coproduct X ⟶ Y :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (coproductDescBased f)

/-- Postcomposing a coproduct inclusion with the induced fold recovers the
original summand morphism. -/
theorem coproductι_comp_desc {S : Scheme.{u}} {I : Type v} [Finite I]
    {X : I → GroupoidsOver S} {Y : GroupoidsOver S} [∀ i, AlgebraicStack (X i)]
    [AlgebraicStack Y] (f : ∀ i, X i ⟶ Y) (i : I) :
    coproductι X i ≫ coproductDesc f = f i :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

/-- The finite disjoint union of algebraic stacks is an algebraic stack. -/
instance instCoproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] :
    AlgebraicStack (GroupoidsOver.coproduct X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
