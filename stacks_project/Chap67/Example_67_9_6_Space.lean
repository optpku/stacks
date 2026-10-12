/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import stacks_project.Chap65.Example_65_14_8_Action
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Lemma_67_9_5_Local

/-!
# The structure morphism of 𝔸¹_k / ℤ is universally closed

This module packages the fppf quotient of Spaces Example 65.14.8 as a Type-u
algebraic space over `Spec(k)` and records that its structure morphism to
`Spec(k)` is universally closed. Same-universe `sheafify` of the quotient
presheaf does not elaborate, so the functor of points is an explicit Type-u
section functor of fppf-local maps to 𝔸¹_k with ℤ-descent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- Restrict a map from an open of `T` into 𝔸¹_k along an inclusion of opens. -/
def restrictToCover {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    {U V : T.left.Opens} (hVU : V ≤ U)
    (f : Over.mk (U.ι ≫ T.hom) ⟶ cover k) :
    Over.mk (V.ι ≫ T.hom) ⟶ cover k :=
  (Over.homMk (T.left.homOfLE hVU) sorry :
      Over.mk (V.ι ≫ T.hom) ⟶ Over.mk (U.ι ≫ T.hom)) ≫
    f

/-- The underlying scheme morphism of `restrictToCover hVU f` is `homOfLE hVU`
composed with `f.left`. -/
theorem restrictToCover_left {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    {U V : T.left.Opens} (hVU : V ≤ U)
    (f : Over.mk (U.ι ≫ T.hom) ⟶ cover k) :
    (restrictToCover hVU f).left = T.left.homOfLE hVU ≫ f.left := sorry

/-- An fppf-local map from a test scheme `T` to 𝔸¹_k with ℤ-descent: a jointly
covering family of open pieces of `T` indexed by the translation group, together
with a map from each piece to the affine line, such that on overlaps the two maps
differ by a translation. -/
structure TranslationSection (k : Type u) [Field k] [CharZero k] (T : Over (base k)) where
  /-- The open piece of `T` labelled by a translation. -/
  piece : group → T.left.Opens
  /-- The pieces jointly cover `T`. -/
  iSup_eq_top : (⨆ n, piece n) = ⊤
  /-- A map from each piece into 𝔸¹_k. -/
  toCover : ∀ n, Over.mk ((piece n).ι ≫ T.hom) ⟶ cover k
  /-- On overlaps, the two maps differ by a translation. -/
  descent :
    ∀ m n, (ofAut (action k)).pointRel (Over.mk ((piece m ⊓ piece n).ι ≫ T.hom))
      (restrictToCover inf_le_left (toCover m))
      (restrictToCover inf_le_right (toCover n))

/-- The quotient section over `T` coming from a global map `T ⟶ 𝔸¹_k`, supported
on the whole of `T` in every translation label. -/
def TranslationSection.ofHom {k : Type u} [Field k] [CharZero k] {T : Over (base k)}
    (f : T ⟶ cover k) : TranslationSection k T where
  piece n := ⊤
  iSup_eq_top := sorry
  toCover n := Over.homMk ((⊤ : T.left.Opens).ι) sorry ≫ f
  descent := sorry

/-- The support of `TranslationSection.ofHom f` is the whole of `T` on every
translation label. -/
theorem TranslationSection.ofHom_piece {k : Type u} [Field k] [CharZero k]
    {T : Over (base k)} (f : T ⟶ cover k) (n : group) :
    (TranslationSection.ofHom f).piece n = ⊤ := sorry

/-- Pull back an fppf-local map with ℤ-descent along a morphism of schemes over
`Spec(k)`. -/
def TranslationSection.restrict {k : Type u} [Field k] [CharZero k]
    {X Y : Over (base k)} (f : Y ⟶ X) (s : TranslationSection k X) :
    TranslationSection k Y where
  piece n := f.left ⁻¹ᵁ s.piece n
  iSup_eq_top := sorry
  toCover n :=
    (Over.homMk (f.left ∣_ s.piece n) sorry :
        Over.mk ((f.left ⁻¹ᵁ s.piece n).ι ≫ Y.hom) ⟶
          Over.mk ((s.piece n).ι ≫ X.hom)) ≫
      s.toCover n
  descent := sorry

/-- The pieces of `TranslationSection.restrict f s` are the inverse images of the
pieces of `s`. -/
theorem TranslationSection.restrict_piece {k : Type u} [Field k] [CharZero k]
    {X Y : Over (base k)} (f : Y ⟶ X) (s : TranslationSection k X) (n : group) :
    (TranslationSection.restrict f s).piece n = f.left ⁻¹ᵁ s.piece n := sorry

/-- Two fppf-local maps with ℤ-descent agree when they differ by a translation on
all overlaps of their covering pieces. -/
def TranslationSection.Rel {k : Type u} [Field k] [CharZero k] (T : Over (base k)) :
    TranslationSection k T → TranslationSection k T → Prop :=
  fun s t ↦ ∀ m n,
    (ofAut (action k)).pointRel (Over.mk ((s.piece m ⊓ t.piece n).ι ≫ T.hom))
      (restrictToCover inf_le_left (s.toCover m))
      (restrictToCover inf_le_right (t.toCover n))

/-- `TranslationSection.Rel` is agreement up to translation on overlaps of
covering pieces. -/
theorem TranslationSection.rel_iff {k : Type u} [Field k] [CharZero k]
    (T : Over (base k)) (s t : TranslationSection k T) :
    TranslationSection.Rel T s t ↔ ∀ m n,
      (ofAut (action k)).pointRel (Over.mk ((s.piece m ⊓ t.piece n).ι ≫ T.hom))
        (restrictToCover inf_le_left (s.toCover m))
        (restrictToCover inf_le_right (t.toCover n)) := sorry

/-- The Type-u fppf sheaf of points of 𝔸¹_k / ℤ, as the quotient of fppf-local
maps to 𝔸¹_k with ℤ-descent by overlap agreement. This is a same-universe model
of `sheafOfPoints`, not the objectwise quotient presheaf. -/
def translationQuotientFunctor (k : Type u) [Field k] [CharZero k] :
    (Over (base k))ᵒᵖ ⥤ Type u where
  obj T := Quot (TranslationSection.Rel (unop T))
  map {X Y} f :=
    TypeCat.ofHom (Quot.map (TranslationSection.restrict (unop f)) (fun _ _ _ ↦ sorry))
  map_id := sorry
  map_comp := sorry

/-- The value of `translationQuotientFunctor k` on `T` is the quotient of
fppf-local maps `T → 𝔸¹_k` with ℤ-descent. -/
theorem translationQuotientFunctor_obj (k : Type u) [Field k] [CharZero k]
    (T : Over (base k)) :
    (translationQuotientFunctor k).obj (op T) = Quot (TranslationSection.Rel T) :=
  sorry

/-- The atlas transformation `yoneda.obj (cover k) ⟶ translationQuotientFunctor k`
sending a global map to its associated fppf-local section. -/
def translationQuotientAtlas (k : Type u) [Field k] [CharZero k] :
    yoneda.obj (cover k) ⟶ translationQuotientFunctor k where
  app T :=
    TypeCat.ofHom fun f ↦
      Quot.mk (TranslationSection.Rel (unop T)) (TranslationSection.ofHom f)
  naturality := sorry

/-- The atlas sends a global map `T ⟶ 𝔸¹_k` to the class of
`TranslationSection.ofHom`. -/
theorem translationQuotientAtlas_app (k : Type u) [Field k] [CharZero k]
    (T : Over (base k)) (f : T ⟶ cover k) :
    (translationQuotientAtlas k).app (op T) f =
      Quot.mk (TranslationSection.Rel T) (TranslationSection.ofHom f) := sorry

/-- The algebraic space 𝔸¹_k / ℤ over Spec(k), presented by the Type-u fppf sheaf
of fppf-local maps to 𝔸¹_k with ℤ-descent. -/
def translationQuotient (k : Type u) [Field k] [CharZero k] : AlgebraicSpace (base k) :=
  ofFunctor (translationQuotientFunctor k) sorry sorry
    ⟨cover k, translationQuotientAtlas k, sorry, sorry⟩

/-- The functor of points of `translationQuotient k` is the Type-u fppf section
functor `translationQuotientFunctor k`. -/
theorem translationQuotient_functorOfPoints (k : Type u) [Field k] [CharZero k] :
    (translationQuotient k).functorOfPoints = translationQuotientFunctor k := sorry

/-- The structure morphism `p : 𝔸¹_k / ℤ ⟶ Spec(k)` of algebraic spaces over
`Spec(k)`. -/
def structureHom (k : Type u) [Field k] [CharZero k] :
    translationQuotient k ⟶ ofOver (Over.mk (𝟙 (base k))) where
  app T := TypeCat.ofHom fun _ ↦ Over.homMk T.unop.hom
  naturality := sorry

/-- The component of `structureHom k` at `T` is the unique morphism
`T.unop ⟶ Over.mk (𝟙 (base k))`. -/
theorem structureHom_app (k : Type u) [Field k] [CharZero k]
    (T : (Over (base k))ᵒᵖ) (x : (translationQuotient k).functorOfPoints.obj T) :
    (structureHom k).app T x = Over.homMk T.unop.hom := sorry

/-- The structure morphism of 𝔸¹_k / ℤ over a characteristic-zero field is
universally closed. -/
instance instUniversallyClosed_structureHom (k : Type u) [Field k] [CharZero k] :
    UniversallyClosed (structureHom k) :=
  sorry

/-- Every scheme-valued base change of `structureHom k` has closed projection on
points, the scheme-valued test of Lemma 67.9.5. -/
theorem forallScheme_structureHom (k : Type u) [Field k] [CharZero k] :
    Closed.forallScheme (structureHom k) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
