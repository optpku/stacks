/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Representable.PullbackDiagonal

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Fibre products of algebraic spaces over a sheaf

If `H` is an fppf sheaf on `Over S` with representable diagonal, and `F`, `G` are algebraic
spaces over `S` equipped with maps of sheaves to `H`, then the sheaf fibre product `F ×_H G`
is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ReasLibPullback

/-- Functor-of-points pullbacks exist in the presheaf category on schemes over `S`. -/
instance instHasPullbacksFunctorOfPoints {S : Scheme.{u}} :
    HasPullbacks ((Over S)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- The presheaf fibre product of algebraic spaces over an fppf sheaf is an fppf sheaf. -/
theorem pullbackOver_isSheaf {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Limits.pullback f g) := by
  apply ObjectProperty.prop_limit (Presheaf.IsSheaf (Scheme.fppfTopology.over S)) (cospan f g)
  rintro (_ | ⟨_ | _⟩)
  all_goals first | exact F.isSheaf | exact G.isSheaf | exact hH

/-- The presheaf fibre product of algebraic spaces over a presheaf with representable diagonal
has representable diagonal. -/
theorem pullbackOver_representableDiagonal {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    yoneda.relativelyRepresentable (Limits.diag (Limits.pullback f g)) :=
  CategoryTheory.Functor.relativelyRepresentable.PullbackDiagonal.diagonal f g F.representableDiagonal G.representableDiagonal hΔ

private theorem locallySurjective_baseChange {S : Scheme.{u}}
    (J : GrothendieckTopology (Over S))
    {P F G H : (Over S)ᵒᵖ ⥤ Type u} {α : P ⟶ F} {β : P ⟶ G}
    {f : F ⟶ H} {g : G ⟶ H} (sq : IsPullback α β f g)
    (hf : Presheaf.IsLocallySurjective J f) : Presheaf.IsLocallySurjective J β := by
  constructor
  intro A s
  refine J.superset_covering ?_ (hf.imageSieve_mem (g.app _ s))
  intro B i hi
  obtain ⟨t, ht⟩ := hi
  obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback
    (sq.map ((evaluation _ _).obj (Opposite.op B))) t (G.map i.op s)
    (by change f.app _ t = g.app _ (G.map i.op s)
        rw [ht, g.naturality_apply])
  exact ⟨z, hz⟩

set_option backward.isDefEq.respectTransparency false in
private theorem atlasPullback_factorization {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {U V W : Over S} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G)
    (α : yoneda.obj W ⟶ yoneda.obj U) (β : yoneda.obj W ⟶ yoneda.obj V)
    (sq : IsPullback α β (a ≫ f) (b ≫ g)) :
    ∃ (K : (Over S)ᵒᵖ ⥤ Type u) (j : yoneda.obj W ⟶ K)
      (q : K ⟶ Limits.pullback f g) (r : K ⟶ yoneda.obj U) (s : K ⟶ G),
      IsPullback β j b s ∧ IsPullback r q a (pullback.fst f g) ∧
        j ≫ q = pullback.lift (α ≫ a) (β ≫ b)
          (by simpa only [Category.assoc] using sq.w) := by
  let K := Limits.pullback (a ≫ f) g
  let q : K ⟶ Limits.pullback f g :=
    pullback.lift (pullback.fst (a ≫ f) g ≫ a) (pullback.snd (a ≫ f) g)
      (by simpa only [Category.assoc] using pullback.condition (f := a ≫ f) (g := g))
  let j : yoneda.obj W ⟶ K := pullback.lift α (β ≫ b)
    (by simpa only [Category.assoc] using sq.w)
  have qfst : q ≫ pullback.fst f g = pullback.fst (a ≫ f) g ≫ a :=
    pullback.lift_fst _ _ _
  have qsnd : q ≫ pullback.snd f g = pullback.snd (a ≫ f) g :=
    pullback.lift_snd _ _ _
  have jfst : j ≫ pullback.fst (a ≫ f) g = α := pullback.lift_fst _ _ _
  have jsnd : j ≫ pullback.snd (a ≫ f) g = β ≫ b := pullback.lift_snd _ _ _
  have sqj : IsPullback β j b (pullback.snd (a ≫ f) g) := by
    apply IsPullback.of_bot (v₂₁ := pullback.fst (a ≫ f) g)
      (v₂₂ := g)
    · simpa only [j, pullback.lift_fst] using sq.flip
    · exact jsnd.symm
    · exact (IsPullback.of_hasPullback (a ≫ f) g).flip
  have sqq : IsPullback (pullback.fst (a ≫ f) g) q a (pullback.fst f g) := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
      qfst.symm
      (fun c ↦ pullback.lift c.fst (c.snd ≫ pullback.snd f g) (by
        rw [← Category.assoc, c.condition, Category.assoc, pullback.condition,
          Category.assoc]))
      (fun c ↦ pullback.lift_fst _ _ _)
      (fun c ↦ by apply pullback.hom_ext <;>
        simp only [Category.assoc, qfst, qsnd, pullback.lift_fst_assoc,
          pullback.lift_snd, c.condition]) ?_)
    intro c m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hm₁
    · have h := congrArg (fun k ↦ k ≫ pullback.snd f g) hm₂
      simpa only [Category.assoc, qsnd, pullback.lift_snd] using h
  have hp : j ≫ q = pullback.lift (α ≫ a) (β ≫ b)
      (by simpa only [Category.assoc] using sq.w) := by
    apply pullback.hom_ext
    · rw [Category.assoc, qfst, ← Category.assoc, jfst, pullback.lift_fst]
    · rw [Category.assoc, qsnd, jsnd, pullback.lift_snd]
  exact ⟨K, j, q, pullback.fst (a ≫ f) g, pullback.snd (a ≫ f) g, sqj, sqq, hp⟩

set_option backward.isDefEq.respectTransparency false in
private theorem atlasPullback_etale {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {U V W : Over S} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G)
    (α : yoneda.obj W ⟶ yoneda.obj U) (β : yoneda.obj W ⟶ yoneda.obj V)
    (sq : IsPullback α β (a ≫ f) (b ≫ g))
    (ha : (MorphismProperty.over (@Etale)).presheaf a)
    (hb : (MorphismProperty.over (@Etale)).presheaf b) :
    (MorphismProperty.over (@Etale)).presheaf
      (pullback.lift (α ≫ a) (β ≫ b)
        (by simpa only [Category.assoc] using sq.w)) := by
  obtain ⟨K, j, q, r, s, sqj, sqq, hp⟩ := atlasPullback_factorization f g a b α β sq
  have hj : (MorphismProperty.over (@Etale)).presheaf j :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.over (@Etale))).of_isPullback sqj hb
  have hq : (MorphismProperty.over (@Etale)).presheaf q :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.over (@Etale))).of_isPullback sqq ha
  rw [← hp]
  apply MorphismProperty.relative.of_exists
    (P := MorphismProperty.inverseImage (@Etale) (Over.forget S))
  intro A t
  refine ⟨hj.rep.pullback (hq.rep.fst t), hj.rep.fst (hq.rep.fst t),
    hj.rep.snd (hq.rep.fst t) ≫ hq.rep.snd t, ?_, ?_⟩
  · simpa only [yoneda.map_comp] using
      (hj.rep.isPullback (hq.rep.fst t)).paste_vert (hq.rep.isPullback t)
  · have h₁ : Etale (hj.rep.snd (hq.rep.fst t)).left := hj.property_snd _
    have h₂ : Etale (hq.rep.snd t).left := hq.property_snd _
    change Etale ((hj.rep.snd (hq.rep.fst t)).left ≫ (hq.rep.snd t).left)
    infer_instance

private theorem atlasPullback_locallySurjective {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {U V W : Over S} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G)
    (α : yoneda.obj W ⟶ yoneda.obj U) (β : yoneda.obj W ⟶ yoneda.obj V)
    (sq : IsPullback α β (a ≫ f) (b ≫ g))
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (pullback.lift (α ≫ a) (β ≫ b)
        (by simpa only [Category.assoc] using sq.w)) := by
  obtain ⟨K, j, q, r, s, sqj, sqq, hp⟩ := atlasPullback_factorization f g a b α β sq
  have hs_j := locallySurjective_baseChange (Scheme.etaleTopology.over S) sqj hb
  have hs_q := locallySurjective_baseChange (Scheme.etaleTopology.over S) sqq ha
  rw [← hp]
  exact Presheaf.isLocallySurjective_comp (Scheme.etaleTopology.over S) j q

set_option backward.isDefEq.respectTransparency false in
private theorem atlasPullback_properties {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {U V W : Over S} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G)
    (α : yoneda.obj W ⟶ yoneda.obj U) (β : yoneda.obj W ⟶ yoneda.obj V)
    (sq : IsPullback α β (a ≫ f) (b ≫ g))
    (ha : (MorphismProperty.over (@Etale)).presheaf a)
    (hsa : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb : (MorphismProperty.over (@Etale)).presheaf b)
    (hsb : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b) :
    let p := pullback.lift (α ≫ a) (β ≫ b)
      (by simpa only [Category.assoc] using sq.w)
    (MorphismProperty.over (@Etale)).presheaf p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨atlasPullback_etale f g a b α β sq ha hb,
    atlasPullback_locallySurjective f g a b α β sq hsa hsb⟩

/-- The presheaf fibre product of algebraic spaces over a presheaf with representable diagonal
admits a representable étale locally-surjective atlas. -/
theorem pullbackOver_hasAtlas {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ Limits.pullback f g),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := by
  let a := F.atlas.choose_spec.choose
  let b := G.atlas.choose_spec.choose
  let r := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  let W := r.pullback (b ≫ g)
  let p : yoneda.obj W ⟶ Limits.pullback f g :=
    Limits.pullback.lift (r.fst (b ≫ g) ≫ a) (yoneda.map (r.snd (b ≫ g)) ≫ b)
      (((Category.assoc _ _ _).trans (r.w (b ≫ g))).trans (Category.assoc _ _ _).symm)
  exact ⟨W, p, atlasPullback_properties f g a b (r.fst (b ≫ g))
    (yoneda.map (r.snd (b ≫ g))) (r.isPullback (b ≫ g))
    F.atlas.choose_spec.choose_spec.1 F.atlas.choose_spec.choose_spec.2
    G.atlas.choose_spec.choose_spec.1 G.atlas.choose_spec.choose_spec.2⟩

/-- The algebraic space `F ×_H G` obtained as the sheaf fibre product of algebraic spaces `F`
and `G` over an fppf sheaf `H` with representable diagonal. -/
def pullbackOver {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) : AlgebraicSpace S :=
  ofFunctor (Limits.pullback f g) (pullbackOver_isSheaf f g hH)
    (pullbackOver_representableDiagonal f g hΔ) (pullbackOver_hasAtlas f g hΔ)

/-- The functor of points of `pullbackOver f g hH hΔ` is the sheaf fibre product of `f` and `g`.
-/
@[simp] theorem pullbackOver_functorOfPoints {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    (pullbackOver f g hH hΔ).functorOfPoints = Limits.pullback f g := rfl

/-- The algebraic space `pullbackOver f g hH hΔ` is an fppf sheaf with representable diagonal
and a representable étale locally-surjective atlas. -/
theorem pullbackOver_spec {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    let X := pullbackOver f g hH hΔ
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨(pullbackOver f g hH hΔ).isSheaf, (pullbackOver f g hH hΔ).representableDiagonal,
    (pullbackOver f g hH hΔ).atlas⟩

/-- The first projection of functors of points for `pullbackOver f g hH hΔ`. -/
def pullbackOverFstNat {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    Limits.pullback f g ⟶ F.functorOfPoints :=
  Limits.pullback.fst f g

/-- The second projection of functors of points for `pullbackOver f g hH hΔ`. -/
def pullbackOverSndNat {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    Limits.pullback f g ⟶ G.functorOfPoints :=
  Limits.pullback.snd f g

/-- The first projection `F ×_H G ⟶ F`. -/
def pullbackOverFst {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOver f g hH hΔ ⟶ F :=
  pullbackOverFstNat f g

/-- The second projection `F ×_H G ⟶ G`. -/
def pullbackOverSnd {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOver f g hH hΔ ⟶ G :=
  pullbackOverSndNat f g

/-- `pullbackOverFstNat f g` is the first projection of the functor-category pullback. -/
theorem pullbackOverFstNat_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    pullbackOverFstNat f g = Limits.pullback.fst f g := rfl

/-- `pullbackOverSndNat f g` is the second projection of the functor-category pullback. -/
theorem pullbackOverSndNat_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    pullbackOverSndNat f g = Limits.pullback.snd f g := rfl

/-- `pullbackOverFst f g hH hΔ` is the first functor-of-points projection. -/
theorem pullbackOverFst_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOverFst f g hH hΔ = pullbackOverFstNat f g := rfl

/-- `pullbackOverSnd f g hH hΔ` is the second functor-of-points projection. -/
theorem pullbackOverSnd_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOverSnd f g hH hΔ = pullbackOverSndNat f g := rfl

/-- The presheaf projections exhibit the fibre product over any presheaf `H`.
No sheaf or representability hypothesis on `H` is needed for this universal property. -/
theorem pullbackOver_isPullback_presheaf {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    IsPullback (pullbackOverFstNat f g) (pullbackOverSndNat f g) f g :=
  IsPullback.of_hasPullback f g

/-- Compatibility wrapper for the presheaf universal property with the hypotheses used
to construct `pullbackOver`. See `pullbackOver_isPullback_presheaf` for the weaker interface. -/
theorem pullbackOver_isPullback {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    IsPullback (pullbackOverFstNat f g) (pullbackOverSndNat f g) f g :=
  pullbackOver_isPullback_presheaf f g

/-- The scheme `U ×_H V` obtained from Yoneda sections `a : yoneda.obj U ⟶ F.functorOfPoints`
and `b : yoneda.obj V ⟶ G.functorOfPoints` by pulling back along the maps to `H`. -/
def pullbackOverAtlas {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) : Over S :=
  let ha := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  ha.pullback (b ≫ g)

/-- `pullbackOverAtlas f g hΔ a b` is the representing object of the pullback of `a ≫ f`
along `b ≫ g`. -/
theorem pullbackOverAtlas_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    pullbackOverAtlas f g hΔ a b =
      (Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)).pullback (b ≫ g) := rfl

/-- The projection `U ×_H V ⟶ U` of the representing pullback of the Yoneda sections to `H`. -/
def pullbackOverAtlasFst {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    yoneda.obj (pullbackOverAtlas f g hΔ a b) ⟶ yoneda.obj U :=
  let ha := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  ha.fst (b ≫ g)

/-- The projection `U ×_H V ⟶ V` of the representing pullback of the Yoneda sections to `H`. -/
def pullbackOverAtlasSnd {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    pullbackOverAtlas f g hΔ a b ⟶ V :=
  let ha := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  ha.snd (b ≫ g)

/-- The atlas morphism `U ×_H V ⟶ F ×_H G` induced by the Yoneda sections `a` and `b`. -/
def pullbackOverAtlasHom {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    yoneda.obj (pullbackOverAtlas f g hΔ a b) ⟶ Limits.pullback f g :=
  Limits.pullback.lift (pullbackOverAtlasFst f g hΔ a b ≫ a)
    (yoneda.map (pullbackOverAtlasSnd f g hΔ a b) ≫ b)
    (((Category.assoc (pullbackOverAtlasFst f g hΔ a b) a f).trans
        ((Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)).w (b ≫ g))).trans
      (Category.assoc (yoneda.map (pullbackOverAtlasSnd f g hΔ a b)) b g).symm)

/-- The square exhibiting `pullbackOverAtlas f g hΔ a b` as the fibre product `U ×_H V`
of the Yoneda sections `a ≫ f` and `b ≫ g` is a pullback. -/
theorem pullbackOverAtlas_isPullback {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    IsPullback (pullbackOverAtlasFst f g hΔ a b)
      (yoneda.map (pullbackOverAtlasSnd f g hΔ a b)) (a ≫ f) (b ≫ g) :=
  (Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)).isPullback (b ≫ g)

/-- Étale Yoneda sections induce an étale atlas map; local surjectivity is not required. -/
theorem pullbackOverAtlasHom_etale {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints)
    (ha_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) a)
    (hb_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) b) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale))
      (pullbackOverAtlasHom f g hΔ a b) :=
  atlasPullback_etale f g a b (pullbackOverAtlasFst f g hΔ a b)
    (yoneda.map (pullbackOverAtlasSnd f g hΔ a b))
    (pullbackOverAtlas_isPullback f g hΔ a b) ha_etale hb_etale

/-- Étale-locally surjective Yoneda sections induce an étale-locally surjective atlas map;
no étaleness assumption on the sections is required. -/
theorem pullbackOverAtlasHom_locallySurjective {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints)
    (ha_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (pullbackOverAtlasHom f g hΔ a b) :=
  atlasPullback_locallySurjective f g a b (pullbackOverAtlasFst f g hΔ a b)
    (yoneda.map (pullbackOverAtlasSnd f g hΔ a b))
    (pullbackOverAtlas_isPullback f g hΔ a b) ha_surj hb_surj

/-- If `a` and `b` are étale and étale-locally surjective, then the induced atlas map is too. -/
theorem pullbackOverAtlasHom_spec {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints)
    (ha_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) a)
    (ha_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) b)
    (hb_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale))
        (pullbackOverAtlasHom f g hΔ a b) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (pullbackOverAtlasHom f g hΔ a b) :=
  ⟨pullbackOverAtlasHom_etale f g hΔ a b ha_etale hb_etale,
    pullbackOverAtlasHom_locallySurjective f g hΔ a b ha_surj hb_surj⟩

/-- The mediating morphism into the algebraic-space pullback induced by a commutative cone. -/
def pullbackLift {S : Scheme.{u}} {W F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H)
    (h : W ⟶ F) (k : W ⟶ G) (w : h ≫ f = k ≫ g) :
    W ⟶ pullbackOver f g H.isSheaf H.representableDiagonal :=
  (pullback.lift (h : W.functorOfPoints ⟶ F.functorOfPoints)
    (k : W.functorOfPoints ⟶ G.functorOfPoints) w :
    W.functorOfPoints ⟶
      (pullbackOver f g H.isSheaf H.representableDiagonal).functorOfPoints)

/-- The mediating morphism recovers the first map of the cone. -/
theorem pullbackLift_fst {S : Scheme.{u}} {W F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H)
    (h : W ⟶ F) (k : W ⟶ G) (w : h ≫ f = k ≫ g) :
    pullbackLift f g h k w ≫ pullbackOverFst f g H.isSheaf H.representableDiagonal = h :=
  Limits.pullback.lift_fst (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (f : F.functorOfPoints ⟶ H.functorOfPoints))
    (g := (g : G.functorOfPoints ⟶ H.functorOfPoints))
    (h : W.functorOfPoints ⟶ F.functorOfPoints) k w

/-- The mediating morphism recovers the second map of the cone. -/
theorem pullbackLift_snd {S : Scheme.{u}} {W F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H)
    (h : W ⟶ F) (k : W ⟶ G) (w : h ≫ f = k ≫ g) :
    pullbackLift f g h k w ≫ pullbackOverSnd f g H.isSheaf H.representableDiagonal = k :=
  Limits.pullback.lift_snd (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (f : F.functorOfPoints ⟶ H.functorOfPoints))
    (g := (g : G.functorOfPoints ⟶ H.functorOfPoints))
    (h : W.functorOfPoints ⟶ F.functorOfPoints) k w

set_option backward.isDefEq.respectTransparency false in
/-- The projections of the algebraic-space pullback satisfy its universal property. -/
theorem isPullback {S : Scheme.{u}} {F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback (pullbackOverFst f g H.isSheaf H.representableDiagonal)
      (pullbackOverSnd f g H.isSheaf H.representableDiagonal) f g := by
  let fp : F.functorOfPoints ⟶ H.functorOfPoints := f
  let gp : G.functorOfPoints ⟶ H.functorOfPoints := g
  let w : pullbackOverFst f g H.isSheaf H.representableDiagonal ≫ f =
      pullbackOverSnd f g H.isSheaf H.representableDiagonal ≫ g :=
    Limits.pullback.condition (f := fp) (g := gp)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun c ↦ pullbackLift f g c.fst c.snd c.condition)
    (fun c ↦ Limits.pullback.lift_fst (f := fp) (g := gp)
      (c.fst : c.pt.functorOfPoints ⟶ F.functorOfPoints) c.snd c.condition)
    (fun c ↦ Limits.pullback.lift_snd (f := fp) (g := gp)
      (c.fst : c.pt.functorOfPoints ⟶ F.functorOfPoints) c.snd c.condition)
    (fun c m hm₁ hm₂ ↦ Limits.pullback.hom_ext (f := fp) (g := gp)
      (hm₁.trans (Limits.pullback.lift_fst (f := fp) (g := gp)
        (c.fst : c.pt.functorOfPoints ⟶ F.functorOfPoints) c.snd c.condition).symm)
      (hm₂.trans (Limits.pullback.lift_snd (f := fp) (g := gp)
        (c.fst : c.pt.functorOfPoints ⟶ F.functorOfPoints) c.snd c.condition).symm)))

/-- A morphism of algebraic spaces admits the explicitly constructed pullback object. -/
instance hasPullback {S : Scheme.{u}} {F G H : AlgebraicSpace S} (f : F ⟶ H) (g : G ⟶ H) :
    HasPullback f g :=
  HasLimit.mk
    { cone := PullbackCone.mk (pullbackOverFst f g H.isSheaf H.representableDiagonal)
        (pullbackOverSnd f g H.isSheaf H.representableDiagonal) (isPullback f g).w
      isLimit := (isPullback f g).isLimit }

/-- The category of algebraic spaces over a scheme has all pullbacks. -/
instance instHasPullbacks {S : Scheme.{u}} : HasPullbacks (AlgebraicSpace S) :=
  hasPullbacks_of_hasLimit_cospan (AlgebraicSpace S)

end AlgebraicGeometry.AlgebraicSpace.ReasLibPullback

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison morphism `X ×_Z Z' ⟶ Y ×_Z Z'` induced by `f : X ⟶ Y`. -/
noncomputable def overBaseChange {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z) :
    pullback (f ≫ h) g ⟶ pullback h g :=
  pullback.lift (pullback.fst (f ≫ h) g ≫ f) (pullback.snd (f ≫ h) g)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := f ≫ h) (g := g)))

/-- The first projection of the base-change comparison is the original first projection
followed by `f`. -/
theorem overBaseChange_fst {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f h g ≫ pullback.fst h g = pullback.fst (f ≫ h) g ≫ f := by
  unfold overBaseChange
  exact pullback.lift_fst _ _ _

/-- The second projection of the base-change comparison is the original second projection.
-/
theorem overBaseChange_snd {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f h g ≫ pullback.snd h g = pullback.snd (f ≫ h) g := by
  unfold overBaseChange
  exact pullback.lift_snd _ _ _

/-- The functor of points of the fibre product of `X` with a scheme over `Y`. -/
def pullbackAlongSchemeFunctorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) : (Over S)ᵒᵖ ⥤ Type u :=
  let fP : X.functorOfPoints ⟶ Y.functorOfPoints := f
  let bP : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints := b
  pullback fP bP

/-- The first projection of the functor-of-points fibre product. -/
def pullbackAlongSchemeFstNat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    pullbackAlongSchemeFunctorOfPoints f b ⟶ X.functorOfPoints :=
  let fP : X.functorOfPoints ⟶ Y.functorOfPoints := f
  let bP : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints := b
  pullback.fst fP bP

/-- The second projection of the functor-of-points fibre product. -/
def pullbackAlongSchemeSndNat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    pullbackAlongSchemeFunctorOfPoints f b ⟶ (ofOver V).functorOfPoints :=
  let fP : X.functorOfPoints ⟶ Y.functorOfPoints := f
  let bP : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints := b
  pullback.snd fP bP

/-- The fibre product `V ×_Y X` of an algebraic space morphism `f : X ⟶ Y` with
a morphism from a scheme `V` over `S`. -/
def pullbackAlongScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : AlgebraicSpace S :=
  ReasLibPullback.pullbackOver f b Y.isSheaf Y.representableDiagonal

namespace pullbackAlongScheme

/-- The projection `V ×_Y X ⟶ X`. -/
def fst {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over S}
    (b : ofOver V ⟶ Y) : pullbackAlongScheme f b ⟶ X :=
  pullbackAlongSchemeFstNat f b

/-- The projection `V ×_Y X ⟶ V`. -/
def snd {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over S}
    (b : ofOver V ⟶ Y) : pullbackAlongScheme f b ⟶ ofOver V :=
  pullbackAlongSchemeSndNat f b

/-- The functor of points of `pullbackAlongScheme f b` is the presheaf pullback. -/
theorem functorOfPoints_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) :
    (pullbackAlongScheme f b).functorOfPoints =
      pullbackAlongSchemeFunctorOfPoints f b :=
  rfl

/-- The two projections of `pullbackAlongScheme f b` commute with `f` and `b`. -/
theorem fst_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : fst f b ≫ f = snd f b ≫ b := by
  dsimp only [fst, snd, pullbackAlongSchemeFstNat, pullbackAlongSchemeSndNat]
  exact Limits.pullback.condition (C := (Over S)ᵒᵖ ⥤ Type u)
    (f := (f : X.functorOfPoints ⟶ Y.functorOfPoints))
    (g := (b : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints))

/-- `V ×_Y X` is a fibre product of `f` and a morphism from a scheme over `Y`. -/
theorem isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) :
    IsPullback (fst f b) (snd f b) f b :=
  ReasLibPullback.isPullback f b

end pullbackAlongScheme

/-- The fibre product `X ×_W V` of an object `g : X ⟶ W` of `Over W` along
`f : V ⟶ W`. -/
def overPullbackObj {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    (g : Over W) : AlgebraicSpace S :=
  ReasLibPullback.pullbackOver g.hom f W.isSheaf W.representableDiagonal

/-- The first projection `X ×_W V ⟶ X`. -/
def overPullbackFst {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    (g : Over W) : overPullbackObj f g ⟶ g.left :=
  ReasLibPullback.pullbackOverFst g.hom f W.isSheaf W.representableDiagonal

/-- The second projection `X ×_W V ⟶ V`, the structure morphism of the
base-changed object over `V`. -/
def overPullbackSnd {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    (g : Over W) : overPullbackObj f g ⟶ V :=
  ReasLibPullback.pullbackOverSnd g.hom f W.isSheaf W.representableDiagonal

/-- The explicit fibre-product projections form a commutative square. -/
@[reassoc]
theorem overPullback_condition {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    overPullbackFst f g ≫ g.hom = overPullbackSnd f g ≫ f :=
  (ReasLibPullback.isPullback g.hom f).w

/-- The pair `(overPullbackFst f g ≫ u.left, overPullbackSnd f g)` is a cone
over `h.hom` and `f`. -/
theorem overPullback_fst_comp {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) {g h : Over W} (u : g ⟶ h) :
    (overPullbackFst f g ≫ u.left) ≫ h.hom = overPullbackSnd f g ≫ f := by
  rw [Category.assoc, Over.w u]
  exact (ReasLibPullback.isPullback g.hom f).w

/-- The morphism `X ×_W V ⟶ X' ×_W V` induced by a morphism of objects of
`Over W`. -/
def overPullbackMap {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W)
    {g h : Over W} (u : g ⟶ h) :
    overPullbackObj f g ⟶ overPullbackObj f h :=
  ReasLibPullback.pullbackLift h.hom f (overPullbackFst f g ≫ u.left) (overPullbackSnd f g)
    (overPullback_fst_comp f u)

/-- The induced map of fibre products commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem overPullbackMap_fst {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) {g h : Over W} (a : g ⟶ h) :
    overPullbackMap f a ≫ overPullbackFst f h = overPullbackFst f g ≫ a.left :=
  ReasLibPullback.pullbackLift_fst _ _ _ _ _

/-- The induced map of fibre products commutes with the projections to `V`. -/
theorem overPullbackMap_snd {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) {g h : Over W} (u : g ⟶ h) :
    overPullbackMap f u ≫ overPullbackSnd f h = overPullbackSnd f g :=
  ReasLibPullback.pullbackLift_snd _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The map of fibre products induced by an identity is the identity. -/
theorem overPullbackMap_id {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    overPullbackMap f (𝟙 g) = 𝟙 (overPullbackObj f g) := by
  apply (ReasLibPullback.isPullback g.hom f).hom_ext
  · change overPullbackMap f (𝟙 g) ≫ overPullbackFst f g =
      𝟙 (overPullbackObj f g) ≫ overPullbackFst f g
    rw [overPullbackMap_fst, Over.id_left, Category.comp_id, Category.id_comp]
  · change overPullbackMap f (𝟙 g) ≫ overPullbackSnd f g =
      𝟙 (overPullbackObj f g) ≫ overPullbackSnd f g
    rw [overPullbackMap_snd, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The map of fibre products induced by a composite is the composite of the induced maps. -/
theorem overPullbackMap_comp {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) {g h k : Over W} (a : g ⟶ h) (b : h ⟶ k) :
    overPullbackMap f (a ≫ b) = overPullbackMap f a ≫ overPullbackMap f b := by
  apply (ReasLibPullback.isPullback k.hom f).hom_ext
  · change overPullbackMap f (a ≫ b) ≫ overPullbackFst f k =
      (overPullbackMap f a ≫ overPullbackMap f b) ≫ overPullbackFst f k
    simp only [Category.assoc, overPullbackMap_fst, overPullbackMap_fst_assoc,
      Over.comp_left]
  · change overPullbackMap f (a ≫ b) ≫ overPullbackSnd f k =
      (overPullbackMap f a ≫ overPullbackMap f b) ≫ overPullbackSnd f k
    simp only [Category.assoc, overPullbackMap_snd]

/-- Slice base change along `f : V ⟶ W`, sending `g : X ⟶ W` to
`X ×_W V ⟶ V`. -/
def overPullback {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W) :
    Over W ⥤ Over V where
  obj g := Over.mk (overPullbackSnd f g)
  map u := Over.homMk (overPullbackMap f u) (overPullbackMap_snd f u)
  map_id g := by
    apply Over.OverMorphism.ext
    exact overPullbackMap_id f g
  map_comp a b := by
    apply Over.OverMorphism.ext
    exact overPullbackMap_comp f a b

/-- The structure morphism of `overPullback f` is the second projection of the
fibre product. -/
theorem overPullback_obj_hom {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    ((overPullback f).obj g).hom = overPullbackSnd f g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The explicit sheaf fibre product and the standard slice pullback are canonically
isomorphic. The comparison retains both fibre-product projections. -/
def overPullbackIso {S : Scheme.{u}} {V W : AlgebraicSpace S} (f : V ⟶ W) :
    overPullback f ≅ Over.pullback f :=
  NatIso.ofComponents
    (fun g ↦ Over.isoMk (ReasLibPullback.isPullback g.hom f).isoPullback
      (ReasLibPullback.isPullback g.hom f).isoPullback_hom_snd)
    (by
      intro g h a
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (overPullbackMap f a ≫ (ReasLibPullback.isPullback h.hom f).isoPullback.hom) ≫
            pullback.fst h.hom f =
          ((ReasLibPullback.isPullback g.hom f).isoPullback.hom ≫
            pullback.lift (pullback.fst g.hom f ≫ a.left) (pullback.snd g.hom f) _) ≫
              pullback.fst h.hom f
        simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
          pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
        exact overPullbackMap_fst f a
      · change (overPullbackMap f a ≫ (ReasLibPullback.isPullback h.hom f).isoPullback.hom) ≫
            pullback.snd h.hom f =
          ((ReasLibPullback.isPullback g.hom f).isoPullback.hom ≫
            pullback.lift (pullback.fst g.hom f ≫ a.left) (pullback.snd g.hom f) _) ≫
              pullback.snd h.hom f
        simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
        exact overPullbackMap_snd f a)

/-- The standard first projection recovers the explicit first projection. -/
@[reassoc (attr := simp)]
theorem overPullbackIso_hom_fst {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    ((overPullbackIso f).hom.app g).left ≫ pullback.fst g.hom f =
      overPullbackFst f g :=
  (ReasLibPullback.isPullback g.hom f).isoPullback_hom_fst

/-- The standard structure map recovers the explicit second projection. -/
@[reassoc (attr := simp)]
theorem overPullbackIso_hom_snd {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    ((overPullbackIso f).hom.app g).left ≫ pullback.snd g.hom f =
      overPullbackSnd f g :=
  (ReasLibPullback.isPullback g.hom f).isoPullback_hom_snd

/-- The inverse comparison retains the first projection as well. -/
@[reassoc (attr := simp)]
theorem overPullbackIso_inv_fst {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    ((overPullbackIso f).inv.app g).left ≫ overPullbackFst f g =
      pullback.fst g.hom f :=
  (ReasLibPullback.isPullback g.hom f).isoPullback_inv_fst

/-- The inverse comparison retains the second projection as well. -/
@[reassoc (attr := simp)]
theorem overPullbackIso_inv_snd {S : Scheme.{u}} {V W : AlgebraicSpace S}
    (f : V ⟶ W) (g : Over W) :
    ((overPullbackIso f).inv.app g).left ≫ overPullbackSnd f g =
      pullback.snd g.hom f :=
  (ReasLibPullback.isPullback g.hom f).isoPullback_inv_snd

end AlgebraicGeometry.AlgebraicSpace
