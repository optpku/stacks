/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Topology.Clopen
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import Mathlib.CategoryTheory.Category.Cat

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

-- Public coproduct formulas use private empty-fibre and transport constructions.
-- Enable this before declaring those helpers so their bodies remain available.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Functor
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The empty open subscheme of a scheme is an empty scheme. -/
private instance instIsEmptyEmptyOpen {X : Scheme.{u}} : IsEmpty (⊥ : X.Opens).toScheme :=
  inferInstanceAs (IsEmpty (∅ : Set X))

/-- The empty open of a test scheme over `S` is an empty object of `Over S`. -/
private instance instIsEmptyEmptyPiece {S : Scheme.{u}} (T : Over S) :
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
private def atlasOver {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Over S :=
  Exists.choose (AlgebraicStack.existsSmoothSurjectiveAtlas (X := X))

/-- The atlas 1-morphism of an algebraic stack, chosen from the smooth surjective atlas. -/
private def atlasHom {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    GroupoidsOver.slice (atlasOver X) ⟶ X :=
  Exists.choose (Exists.choose_spec (AlgebraicStack.existsSmoothSurjectiveAtlas (X := X)))

/-- The image of the identity object of the atlas slice under the atlas 1-morphism. -/
private def atlasObj {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : X.total :=
  (FiberedCategoryOver.Groupoids.toFunctor (atlasHom X)).obj (Over.mk (𝟙 (atlasOver X)))

/-- The unique morphism in `Over S` out of an empty test scheme. -/
private def emptyOverHom {S : Scheme.{u}} (T U : Over S) [IsEmpty T.left] : T ⟶ U :=
  Over.homMk (isInitialOfIsEmpty.to U.left)
    (isInitialOfIsEmpty.hom_ext (isInitialOfIsEmpty.to U.left ≫ U.hom) T.hom)

/-- An object of an algebraic stack over an empty test scheme, obtained by cartesian
pullback of the atlas object along the unique map from the empty scheme. -/
private def emptyObj {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (T : Over S) [IsEmpty T.left] : X.total :=
  IsPreFibered.pullbackObj (p := X.p) rfl (emptyOverHom T (X.p.obj (atlasObj X)))

/-- The cartesian arrow from `emptyObj X T` to the atlas object. -/
private def emptyObj_toAtlas {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (T : Over S) [IsEmpty T.left] :
    emptyObj X T ⟶ atlasObj X :=
  IsPreFibered.pullbackMap (p := X.p) rfl (emptyOverHom T (X.p.obj (atlasObj X)))

/-- The projection of an algebraic stack is fibered, so cartesian atlas pullbacks are
strongly cartesian. -/
private instance instIsFibered_p {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    X.p.IsFibered :=
  (inferInstance : Functor.IsFibered.InGroupoids X.p).toIsFibered

/-- The atlas pullback of an empty test scheme is cartesian. -/
private instance emptyObj_toAtlas.isCartesian {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (T : Over S) [IsEmpty T.left] :
    X.p.IsCartesian (emptyOverHom T (X.p.obj (atlasObj X))) (emptyObj_toAtlas X T) :=
  IsPreFibered.pullbackMap.IsCartesian (p := X.p) rfl
    (emptyOverHom T (X.p.obj (atlasObj X)))

/-- The atlas pullback of an empty test scheme is strongly cartesian. -/
private instance emptyObj_toAtlas.isStronglyCartesian {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (T : Over S) [IsEmpty T.left] :
    X.p.IsStronglyCartesian (emptyOverHom T (X.p.obj (atlasObj X)))
      (emptyObj_toAtlas X T) :=
  IsFibered.isStronglyCartesian_of_isCartesian X.p
    (emptyOverHom T (X.p.obj (atlasObj X))) (emptyObj_toAtlas X T)

/-- Functoriality of `emptyObj` along a morphism of empty test schemes, induced by the
universal property of the cartesian atlas pullback. -/
private def emptyObj_map {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
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
private def coproductSummandHom_eqRec {S : Scheme.{u}} {I : Type v}
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
def coproductCategory {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) : Cat.{u, u + 1} where
  α := coproductTotal X
  str :=
    { Hom := coproductHom
      id := coproductHom.id
      comp := coproductHom.comp
      id_comp := sorry
      comp_id := sorry
      assoc := sorry }

/-- Inclusion of a summand object into the stack coproduct. -/
def coproductιFunctor {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] (i : I) :
    (X i).total ⥤ coproductCategory X where
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
    (X : I → GroupoidsOver S) : coproductCategory X ⥤ Over S where
  obj a := a.base
  map f := f.base
  map_id := sorry
  map_comp := sorry

/-- The coproduct projection sends an object to its underlying test scheme. -/
@[simp]
theorem coproductFunctor_obj {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) (a : coproductCategory X) :
    (coproductFunctor X).obj a = a.base := rfl

/-- The coproduct projection sends an arrow to its underlying test-scheme morphism. -/
@[simp]
theorem coproductFunctor_map {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) {a b : coproductCategory X} (f : a ⟶ b) :
    (coproductFunctor X).map f = f.base := rfl

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

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

/-- The finite disjoint union of algebraic stacks is an algebraic stack. -/
instance instCoproduct {S : Scheme.{u}} {I : Type v} [Finite I]
    (X : I → GroupoidsOver S) [∀ i, AlgebraicStack (X i)] :
    AlgebraicStack (GroupoidsOver.coproduct X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
