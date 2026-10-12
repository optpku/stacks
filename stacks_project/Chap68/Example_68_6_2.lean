/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import stacks_project.Chap65.Example_65_14_8_Space
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_4_3_Fibre

/-!
# The algebraic space 𝔸¹_k / ℤ is not decent

This module packages the fppf quotient sheaf of Spaces Example 65.14.8 as a Type-u
algebraic space and records that its quoted generic point is not represented by a
monomorphism from the spectrum of a field, so the space is not decent. The source
special case is 𝔸¹_ℚ / ℤ. Same-universe `sheafify` of the quotient presheaf does not
elaborate, as in Example 65.14.9, so the functor of points is an explicit Type-u
section functor of fppf-local maps to 𝔸¹_k with ℤ-descent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The empty open of a scheme is an empty scheme. -/
instance {X : Scheme.{u}} : IsEmpty (⊥ : X.Opens).toScheme :=
  inferInstanceAs (IsEmpty (∅ : Set X))

/-- The empty open of a test scheme over `Spec k` is an empty object of `Over (base k)`. -/
instance {k : Type u} [Field k] [CharZero k] (T : Over (base k)) :
    IsEmpty (Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom)).left :=
  inferInstanceAs (IsEmpty (⊥ : T.left.Opens).toScheme)

/-- The unique morphism from an empty open of `T` into `𝔸¹_k`. -/
def emptyOpenToCover {k : Type u} [Field k] [CharZero k] (T : Over (base k)) :
    Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom) ⟶ cover k :=
  Over.homMk (isInitialOfIsEmpty.to (cover k).left) sorry

/-- The underlying scheme morphism of `emptyOpenToCover T` is the unique map from the empty
scheme. -/
theorem emptyOpenToCover_left {k : Type u} [Field k] [CharZero k] (T : Over (base k)) :
    (emptyOpenToCover T).left = isInitialOfIsEmpty.to (cover k).left := sorry

/-- Restrict a map from an open of `T` into `𝔸¹_k` along an inclusion of opens. -/
def restrictOpen {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    {U V : T.left.Opens} (hVU : V ≤ U)
    (f : Over.mk (U.ι ≫ T.hom) ⟶ cover k) :
    Over.mk (V.ι ≫ T.hom) ⟶ cover k :=
  (Over.homMk (T.left.homOfLE hVU) sorry :
      Over.mk (V.ι ≫ T.hom) ⟶ Over.mk (U.ι ≫ T.hom)) ≫
    f

/-- The underlying scheme morphism of `restrictOpen hVU f` is `homOfLE hVU` composed with
`f.left`. -/
theorem restrictOpen_left {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    {U V : T.left.Opens} (hVU : V ≤ U)
    (f : Over.mk (U.ι ≫ T.hom) ⟶ cover k) :
    (restrictOpen hVU f).left = T.left.homOfLE hVU ≫ f.left := sorry

/-- An fppf-local map from a test scheme `T` to `𝔸¹_k` with ℤ-descent: a jointly covering
family of open pieces of `T` indexed by the translation group (open immersions are fppf),
together with a map from each piece to the affine line, such that on overlaps the two maps
differ by a translation. -/
structure QuotientSection (k : Type u) [Field k] [CharZero k] (T : Over (base k)) where
  /-- The open piece of `T` labelled by a translation. -/
  piece : group → T.left.Opens
  /-- The pieces jointly cover `T`. -/
  iSup_eq_top : (⨆ n, piece n) = ⊤
  /-- A map from each piece into `𝔸¹_k`. -/
  toCover : ∀ n, Over.mk ((piece n).ι ≫ T.hom) ⟶ cover k
  /-- On overlaps, the two maps differ by a translation. -/
  descent :
    ∀ m n, (ofAut (action k)).pointRel (Over.mk ((piece m ⊓ piece n).ι ≫ T.hom))
      (restrictOpen inf_le_left (toCover m)) (restrictOpen inf_le_right (toCover n))

/-- The quotient section over `T` coming from a global map `T ⟶ 𝔸¹_k`, supported on the
identity translation with empty pieces elsewhere. -/
def QuotientSection.ofHom {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    (f : T ⟶ cover k) : QuotientSection k T where
  piece n := if n = 1 then ⊤ else ⊥
  iSup_eq_top := sorry
  toCover n :=
    if h : n = 1 then
      Eq.mp (congrArg (fun U : T.left.Opens ↦ Over.mk (U.ι ≫ T.hom) ⟶ cover k)
        (if_pos h).symm)
        (Over.homMk ((⊤ : T.left.Opens).ι) sorry ≫ f)
    else
      Eq.mp (congrArg (fun U : T.left.Opens ↦ Over.mk (U.ι ≫ T.hom) ⟶ cover k)
        (if_neg h).symm)
        (emptyOpenToCover T)
  descent := sorry

/-- The support of `QuotientSection.ofHom f` is the whole of `T` on the identity translation
and empty on every other label. -/
theorem QuotientSection.ofHom_piece {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    (f : T ⟶ cover k) (n : group) :
    (QuotientSection.ofHom f).piece n = if n = 1 then ⊤ else ⊥ := sorry

/-- Pull back an fppf-local map with ℤ-descent along a morphism of schemes over `Spec k`. -/
def QuotientSection.restrict {k : Type u} [Field k] [CharZero k] {X Y : Over (base k)}
    (f : Y ⟶ X) (s : QuotientSection k X) : QuotientSection k Y where
  piece n := f.left ⁻¹ᵁ s.piece n
  iSup_eq_top := sorry
  toCover n :=
    (Over.homMk (f.left ∣_ s.piece n) sorry :
        Over.mk ((f.left ⁻¹ᵁ s.piece n).ι ≫ Y.hom) ⟶
          Over.mk ((s.piece n).ι ≫ X.hom)) ≫
      s.toCover n
  descent := sorry

/-- Two fppf-local maps with ℤ-descent agree when they differ by a translation on all overlaps
of their covering pieces. -/
def QuotientSection.Rel {k : Type u} [Field k] [CharZero k] (T : Over (base k)) :
    QuotientSection k T → QuotientSection k T → Prop :=
  fun s t ↦ ∀ m n,
    (ofAut (action k)).pointRel (Over.mk ((s.piece m ⊓ t.piece n).ι ≫ T.hom))
      (restrictOpen inf_le_left (s.toCover m)) (restrictOpen inf_le_right (t.toCover n))

/-- `QuotientSection.Rel` is agreement up to translation on overlaps of covering pieces. -/
theorem QuotientSection.rel_iff {k : Type u} [Field k] [CharZero k] (T : Over (base k))
    (s t : QuotientSection k T) :
    QuotientSection.Rel T s t ↔ ∀ m n,
      (ofAut (action k)).pointRel (Over.mk ((s.piece m ⊓ t.piece n).ι ≫ T.hom))
        (restrictOpen inf_le_left (s.toCover m))
        (restrictOpen inf_le_right (t.toCover n)) := sorry

/-- The Type-u fppf sheaf of points of `𝔸¹_k / ℤ`, as the quotient of fppf-local maps to
`𝔸¹_k` with ℤ-descent by overlap agreement. This is a same-universe model of
`sheafOfPoints`, not the objectwise quotient presheaf. -/
def spaceFunctor (k : Type u) [Field k] [CharZero k] : (Over (base k))ᵒᵖ ⥤ Type u where
  obj T := Quot (QuotientSection.Rel (unop T))
  map {X Y} f :=
    TypeCat.ofHom <|
      Quot.map (QuotientSection.restrict (unop f)) (fun _ _ _ ↦ sorry)
  map_id := sorry
  map_comp := sorry

/-- The value of `spaceFunctor k` on `T` is the quotient of fppf-local maps `T → 𝔸¹_k` with
ℤ-descent. -/
theorem spaceFunctor_obj (k : Type u) [Field k] [CharZero k] (T : Over (base k)) :
    (spaceFunctor k).obj (op T) = Quot (QuotientSection.Rel T) := sorry

/-- The atlas transformation `yoneda.obj (cover k) ⟶ spaceFunctor k` sending a global map
to its associated fppf-local section. -/
def spaceAtlasHom (k : Type u) [Field k] [CharZero k] :
    yoneda.obj (cover k) ⟶ spaceFunctor k where
  app T :=
    TypeCat.ofHom fun f ↦
      Quot.mk (QuotientSection.Rel (unop T)) (QuotientSection.ofHom f)
  naturality := sorry

/-- The objectwise quotient presheaf of `ofAut (action k)` maps to `spaceFunctor k` by
sending a global map to its associated fppf-local section. -/
def quotientPresheafToSpaceFunctor (k : Type u) [Field k] [CharZero k] :
    (ofAut (action k)).quotientPresheaf ⟶ spaceFunctor k where
  app T :=
    TypeCat.ofHom <|
      Quot.lift
        (fun f : unop T ⟶ cover k ↦
          Quot.mk (QuotientSection.Rel (unop T)) (QuotientSection.ofHom f))
        (fun _ _ _ ↦ sorry)
  naturality := sorry

/-- `quotientPresheafToSpaceFunctor k` sends a represented point to the class of
`QuotientSection.ofHom`. -/
theorem quotientPresheafToSpaceFunctor_mk (k : Type u) [Field k] [CharZero k]
    (T : Over (base k)) (f : T ⟶ cover k) :
    (quotientPresheafToSpaceFunctor k).app (op T)
        (Quot.mk ((ofAut (action k)).pointRel T) f) =
      Quot.mk (QuotientSection.Rel T) (QuotientSection.ofHom f) := sorry

/-- The algebraic space 𝔸¹_k / ℤ over Spec k, presented by the Type-u fppf sheaf of
fppf-local maps to 𝔸¹_k with ℤ-descent. The source special case is 𝔸¹_ℚ / ℤ. -/
def space (k : Type u) [Field k] [CharZero k] : AlgebraicSpace (base k) :=
  ofFunctor (spaceFunctor k) sorry sorry ⟨cover k, spaceAtlasHom k, sorry, sorry⟩

/-- The functor of points of `space k` is the Type-u fppf section functor `spaceFunctor k`. -/
theorem space_functorOfPoints (k : Type u) [Field k] [CharZero k] :
    (space k).functorOfPoints = spaceFunctor k := sorry

/-- The comparison from the universe-raised sheafification of the quotient presheaf to the
universe lift of `spaceFunctor k`, induced by `quotientPresheafToSpaceFunctor`. -/
def functorOfPoints_uliftHom (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (base k)).sheafify
        ((ofAut (action k)).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) ⟶
      spaceFunctor k ⋙ uliftFunctor.{u + 1, u} :=
  (Scheme.fppfTopology.over (base k)).sheafifyLift
    (Functor.whiskerRight (quotientPresheafToSpaceFunctor k) uliftFunctor.{u + 1, u}) sorry

/-- After universe lift, `toSheafify` of the quotient presheaf followed by
`functorOfPoints_uliftHom` recovers the lift of `quotientPresheafToSpaceFunctor`. -/
theorem toSheafify_comp_uliftHom (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (base k)).toSheafify
          ((ofAut (action k)).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) ≫
        functorOfPoints_uliftHom k =
      Functor.whiskerRight (quotientPresheafToSpaceFunctor k) uliftFunctor.{u + 1, u} := sorry

/-- The comparison `functorOfPoints_uliftHom k` identifies the sheafification of the
universe-raised quotient presheaf with the universe lift of `spaceFunctor k`, hence of
`(space k).functorOfPoints`. -/
theorem functorOfPoints_ulift (k : Type u) [Field k] [CharZero k] :
    IsIso (functorOfPoints_uliftHom k) := sorry

/-- The atlas morphism 𝔸¹_k ⟶ 𝔸¹_k / ℤ of algebraic spaces over Spec k. -/
def spaceAtlas (k : Type u) [Field k] [CharZero k] : ofOver (cover k) ⟶ space k :=
  spaceAtlasHom k

/-- `spaceAtlas k` is the canonical projection onto the Type-u fppf quotient sheaf. -/
theorem spaceAtlas_eq (k : Type u) [Field k] [CharZero k] :
    spaceAtlas k = spaceAtlasHom k := sorry

/-- The morphism γ : Spec(k(x)) ⟶ 𝔸¹_k / ℤ of algebraic spaces over Spec k, the
Type-u image of `genericHom`. -/
def genericToSpace (k : Type u) [Field k] [CharZero k] :
    ofOver (genericOver k) ⟶ space k :=
  ofOverMap (genericToCover k) ≫ spaceAtlas k

/-- `genericToSpace k` is the composite of the represented generic-point map with the
sheaf-level atlas. -/
theorem genericToSpace_eq (k : Type u) [Field k] [CharZero k] :
    genericToSpace k = ofOverMap (genericToCover k) ≫ spaceAtlas k := sorry

/-- The field-valued point of 𝔸¹_k / ℤ represented by γ : Spec(k(x)) ⟶ 𝔸¹_k / ℤ. -/
def genericFieldValuedPoint (k : Type u) [Field k] [CharZero k] :
    FieldValuedPoint (space k) :=
  FieldValuedPoint.of (genericResidueField k) (genericStructure k) (genericToSpace k)

/-- The morphism of `genericFieldValuedPoint k` is `genericToSpace k`. -/
theorem genericFieldValuedPoint_hom (k : Type u) [Field k] [CharZero k] :
    (genericFieldValuedPoint k).hom = genericToSpace k := sorry

/-- The quoted generic point of 𝔸¹_k / ℤ, as a point of `|space k|`. -/
def genericSpacePoint (k : Type u) [Field k] [CharZero k] : Points (space k) :=
  Points.mk (genericFieldValuedPoint k)

/-- `genericSpacePoint k` is the class of `genericFieldValuedPoint k`. -/
theorem mk_genericFieldValuedPoint (k : Type u) [Field k] [CharZero k] :
    genericSpacePoint k = Points.mk (genericFieldValuedPoint k) := sorry

/-- Example 68.6.2 (1): the quoted generic point of the algebraic space 𝔸¹_ℚ / ℤ
cannot be represented by a monomorphism from the spectrum of a field. -/
@[stacks 03ID]
theorem not_existsMono_genericPoint :
    ¬ existsMonoFieldValuedPoint (space ℚ) (genericSpacePoint ℚ) := sorry

/-- Example 68.6.2 (2): the algebraic space 𝔸¹_ℚ / ℤ constructed in Spaces,
Example 65.14.8 is not decent. -/
@[stacks 03ID]
theorem not_isDecent :
    ¬ IsDecent (space ℚ) := sorry


end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
