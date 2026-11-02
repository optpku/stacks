/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Ph covering families of algebraic spaces

A ph covering of an algebraic space is a pointwise locally-of-finite-type
indexed family such that every test morphism from an affine scheme admits a
standard ph covering refining the pullback family.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `S` induced by a chart of a standard
ph covering of an affine scheme `Z` over `S`. -/
def ofStandardPhCoverMap {S : Scheme.{u}} {Z : Over S} [IsAffine Z.left]
    (Φ : StandardPhCovering Z.left) (j : Fin Φ.m) :
    ofOver (Over.mk (Φ.map j ≫ Z.hom)) ⟶ ofOver Z :=
  ofOverMap (Over.homMk (Φ.map j) rfl : Over.mk (Φ.map j ≫ Z.hom) ⟶ Z)

/-- `ofStandardPhCoverMap Φ j` is `ofOverMap` of the corresponding morphism in
`Over S`. -/
theorem ofStandardPhCoverMap_eq {S : Scheme.{u}} {Z : Over S}
    [IsAffine Z.left] (Φ : StandardPhCovering Z.left) (j : Fin Φ.m) :
    ofStandardPhCoverMap Φ j =
      ofOverMap (Over.homMk (Φ.map j) rfl : Over.mk (Φ.map j ≫ Z.hom) ⟶ Z) :=
  rfl

/-- A scheme-level standard ph covering of `Z`, viewed as a family of morphisms
of algebraic spaces over `ofOver Z`. -/
def ofStandardPhCover {S : Scheme.{u}} {Z : Over S} [IsAffine Z.left]
    (Φ : StandardPhCovering Z.left) :
    SemiRepresentableFamily.Over (ofOver Z) :=
  SemiRepresentableFamily.Over.ofArrows
    (fun j : Fin Φ.m ↦ ofOver (Over.mk (Φ.map j ≫ Z.hom)))
    (fun j : Fin Φ.m ↦ ofStandardPhCoverMap Φ j)

/-- The `j`-th object of `ofStandardPhCover Φ` is the chart morphism of
algebraic spaces associated to `Φ.map j`. -/
theorem ofStandardPhCover_obj {S : Scheme.{u}} {Z : Over S}
    [IsAffine Z.left] (Φ : StandardPhCovering Z.left) (j : Fin Φ.m) :
    (ofStandardPhCover Φ).obj j = Over.mk (ofStandardPhCoverMap Φ j) :=
  rfl

/-- The pullback family `{X_i ×_X U ⟶ U}` of an indexed family over `X` along a
morphism `h : ofOver Z ⟶ X`. -/
def phCoveringPullback {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) {Z : Over S}
    (h : ofOver Z ⟶ X) : SemiRepresentableFamily.Over (ofOver Z) :=
  SemiRepresentableFamily.Over.ofArrows
    (fun i ↦ overPullbackObj h (Over.mk (f i)))
    (fun i ↦ overPullbackSnd h (Over.mk (f i)))

/-- The `i`-th object of `phCoveringPullback Xi f h` is the slice object of the
base change of `f i` along `h`. -/
theorem phCoveringPullback_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X)
    {Z : Over S} (h : ofOver Z ⟶ X) (i : ι) :
    (phCoveringPullback Xi f h).obj i =
      Over.mk (overPullbackSnd h (Over.mk (f i))) :=
  rfl

/-- An indexed family of morphisms of algebraic spaces over `S` is a ph
covering when each morphism is locally of finite type and every test morphism
from an affine scheme admits a standard ph covering refining the pullback
family. -/
@[mk_iff]
class PhCovering {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) : Prop where
  /-- Every member of the family is locally of finite type. -/
  locallyOfFiniteType : ∀ i, LocallyOfFiniteType (f i)
  /-- Every morphism from an affine scheme to `X` admits a standard ph covering
  refining the pulled-back family `{X_i ×_X U ⟶ U}`. -/
  exists_standardRefinement :
    ∀ {Z : Over S} [IsAffine Z.left] (h : ofOver Z ⟶ X),
      ∃ Φ : StandardPhCovering Z.left,
        SemiRepresentableFamily.Over.Refines (ofStandardPhCover Φ)
          (phCoveringPullback Xi f h)

namespace PhCovering

/-- The identity family `{𝟙 X}` is a ph covering. -/
instance instId {S : Scheme.{u}} {X : AlgebraicSpace S} :
    PhCovering (fun _ : PUnit ↦ X) (fun _ ↦ 𝟙 X) :=
  by
    constructor
    · intro i
      constructor
      intro U V a b g ha hb w
      change a ≫ 𝟙 X.functorOfPoints = yoneda.map g ≫ b at w
      have hw : yoneda.map (𝟙 U) ≫ a = yoneda.map g ≫ b := by
        simpa using w
      let k : U ⟶ ha.rep.pullback b := ha.rep.lift' (𝟙 U) g hw
      have hk : k ≫ ha.rep.fst' b = 𝟙 U := ha.rep.lift'_fst (𝟙 U) g hw
      haveI : AlgebraicGeometry.LocallyOfFiniteType
          (k.left ≫ (ha.rep.fst' b).left) := by
        change AlgebraicGeometry.LocallyOfFiniteType (k ≫ ha.rep.fst' b).left
        rw [hk]
        infer_instance
      haveI : AlgebraicGeometry.LocallyOfFiniteType k.left :=
        AlgebraicGeometry.locallyOfFiniteType_of_comp k.left (ha.rep.fst' b).left
      haveI : AlgebraicGeometry.Etale (ha.rep.snd b).left := ha.property_snd b
      have hg : k ≫ ha.rep.snd b = g := ha.rep.lift'_snd (𝟙 U) g hw
      rw [← hg]
      change AlgebraicGeometry.LocallyOfFiniteType (k.left ≫ (ha.rep.snd b).left)
      infer_instance
    · intro Z _ h
      let Φ : StandardPhCovering Z.left :=
        { m := 1
          source := Z.left
          toBase := 𝟙 Z.left
          isProper_toBase := inferInstance
          surjective_toBase := inferInstance
          cover := fun _ ↦ ⟨⊤, isAffineOpen_top Z.left⟩
          cover_eq_top := by simp }
      refine ⟨Φ, ⟨{ α := fun _ ↦ PUnit.unit, f := fun j ↦ ?_ }⟩⟩
      exact Over.homMk
        (ReasLibPullback.pullbackLift (𝟙 X) h
          (ofStandardPhCoverMap Φ j ≫ h) (ofStandardPhCoverMap Φ j) (by simp))
        (ReasLibPullback.pullbackLift_snd _ _ _ _ _)

/-- Every member of a ph covering family is locally of finite type. -/
instance instLocallyOfFiniteType {S : Scheme.{u}} {ι : Type v}
    {X : AlgebraicSpace S} {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X}
    [PhCovering Xi f] (i : ι) : LocallyOfFiniteType (f i) :=
  ‹PhCovering Xi f›.locallyOfFiniteType i

/-- A ph covering family is locally of finite type and every affine test
morphism admits a standard ph refinement of the pullback family. -/
theorem source_spec {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    (Xi : ι → AlgebraicSpace S) (f : ∀ i, Xi i ⟶ X) [PhCovering Xi f] :
    (∀ i, LocallyOfFiniteType (f i)) ∧
      ∀ {Z : Over S} [IsAffine Z.left] (h : ofOver Z ⟶ X),
        ∃ Φ : StandardPhCovering Z.left,
          SemiRepresentableFamily.Over.Refines (ofStandardPhCover Φ)
            (phCoveringPullback Xi f h) :=
  ⟨PhCovering.locallyOfFiniteType, PhCovering.exists_standardRefinement⟩

/-- For a ph covering family of `X`, every morphism from an affine scheme to
`X` admits a standard ph covering whose charts map to selected members of the
family, with all refinement triangles over `X` commuting. -/
theorem exists_indices {S : Scheme.{u}} {ι : Type v} {X : AlgebraicSpace S}
    {Xi : ι → AlgebraicSpace S} {f : ∀ i, Xi i ⟶ X} [PhCovering Xi f]
    {Z : Over S} [IsAffine Z.left] (h : ofOver Z ⟶ X) :
    ∃ (Φ : StandardPhCovering Z.left) (α : Fin Φ.m → ι)
      (φ : ∀ j, ofOver (Over.mk (Φ.map j ≫ Z.hom)) ⟶ Xi (α j)),
      ∀ j, φ j ≫ f (α j) = ofStandardPhCoverMap Φ j ≫ h :=
  by
    obtain ⟨Φ, ⟨r⟩⟩ := PhCovering.exists_standardRefinement (Xi := Xi) (f := f) h
    refine ⟨Φ, r.α,
      fun j ↦ (r.f j).left ≫ overPullbackFst h (Over.mk (f (r.α j))), ?_⟩
    intro j
    calc
      ((r.f j).left ≫ overPullbackFst h (Over.mk (f (r.α j)))) ≫ f (r.α j) =
          (r.f j).left ≫ (overPullbackFst h (Over.mk (f (r.α j))) ≫ f (r.α j)) :=
        Category.assoc _ _ _
      _ = (r.f j).left ≫ (overPullbackSnd h (Over.mk (f (r.α j))) ≫ h) :=
        congrArg (fun k ↦ (r.f j).left ≫ k) (ReasLibPullback.isPullback (f (r.α j)) h).w
      _ = ((r.f j).left ≫ overPullbackSnd h (Over.mk (f (r.α j)))) ≫ h :=
        (Category.assoc _ _ _).symm
      _ = ofStandardPhCoverMap Φ j ≫ h :=
        congrArg (fun k ↦ k ≫ h) (Over.w (r.f j))

end PhCovering

/-- If `X` and every `X_i` are representable, a ph covering of algebraic spaces
is the same as a ph covering of schemes. -/
theorem phCovering_ofOver_iff {S : Scheme.{u}} {T : Over S} {ι : Type v}
    (U : ι → Over S) (f : ∀ i, U i ⟶ T) :
    PhCovering (fun i ↦ ofOver (U i)) (fun i ↦ ofOverMap (f i)) ↔
      _root_.AlgebraicGeometry.PhCovering (fun i ↦ (U i).left)
        (fun i ↦ (f i).left) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
