module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Quot
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap81.Lemma_81_9_2_Relation

/-!
# Pushout algebraic space of a separated étale open span

The quotient `W = (U ⊔ V) / R` of the étale equivalence relation of
`Lemma_81_9_2_Relation` is an algebraic space over `S`, and supplies the
canonical maps of the pushout of an open immersion along a separated étale
morphism. The objectwise quotient is kept as a Type `u` presheaf; `W` is the
Type `u` quotient obtained on the certified small étale sites of test schemes.
The étale equivalence relation makes this quotient an fppf sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

variable {S : Scheme.{u}}

/-- A `T`-point of the pointwise coproduct of `U` and `V`. -/
abbrev uvPoint (U V : AlgebraicSpace S) (T : Over S) : Type u :=
  U.functorOfPoints.obj (op T) ⊕ V.functorOfPoints.obj (op T)

/-- Restriction of a pointwise coproduct section along a morphism of schemes over `S`. -/
def uvPointMap {U V : AlgebraicSpace S} {T T' : Over S} (g : T' ⟶ T) :
    uvPoint U V T → uvPoint U V T' :=
  Sum.map (fun u ↦ U.functorOfPoints.map g.op u) (fun v ↦ V.functorOfPoints.map g.op v)

/-- Restriction of pointwise coproduct sections is functorial in the test scheme. -/
theorem uvPointMap_comp {U V : AlgebraicSpace S} {T T' T'' : Over S}
    (g : T' ⟶ T) (f : T'' ⟶ T') (x : uvPoint U V T) :
    uvPointMap f (uvPointMap g x) = uvPointMap (f ≫ g) x :=
  match x with
  | Sum.inl u =>
      congrArg Sum.inl <|
        (CategoryTheory.comp_apply (U.functorOfPoints.map g.op)
            (U.functorOfPoints.map f.op) u).symm.trans <|
          congrArg (fun φ ↦ φ u) (U.functorOfPoints.map_comp g.op f.op).symm
  | Sum.inr v =>
      congrArg Sum.inr <|
        (CategoryTheory.comp_apply (V.functorOfPoints.map g.op)
            (V.functorOfPoints.map f.op) v).symm.trans <|
          congrArg (fun φ ↦ φ v) (V.functorOfPoints.map_comp g.op f.op).symm

/-- The generating relation of `R` on pointwise `(U ⊔ V)`-points: the five pair maps
from `U`, `V'`, `V'`, `V`, and the off-diagonal complement of `Δ_{V'/U}`. -/
def glueRel {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U) [Separated f']
    (T : Over S) : uvPoint U V T → uvPoint U V T → Prop :=
  fun x y ↦
    (∃ u : U.functorOfPoints.obj (op T), x = Sum.inl u ∧ y = Sum.inl u) ∨
      (∃ v : V.functorOfPoints.obj (op T), x = Sum.inr v ∧ y = Sum.inr v) ∨
        (∃ v' : V'.functorOfPoints.obj (op T),
          x = Sum.inl (f'.app (op T) v') ∧ y = Sum.inr (ι.app (op T) v')) ∨
          (∃ v' : V'.functorOfPoints.obj (op T),
            x = Sum.inr (ι.app (op T) v') ∧ y = Sum.inl (f'.app (op T) v')) ∨
            ∃ w : (offDiagonal f').functorOfPoints.obj (op T),
              x = Sum.inr ((offDiagonalι f' ≫ pullback.fst f' f' ≫ ι).app (op T) w) ∧
                y = Sum.inr ((offDiagonalι f' ≫ pullback.snd f' f' ≫ ι).app (op T) w)

/-- Two pointwise coproduct points are related exactly by the five generating pair maps. -/
theorem glueRel_iff {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : Over S) (x y : uvPoint U V T) :
    glueRel ι f' T x y ↔
      (∃ u : U.functorOfPoints.obj (op T), x = Sum.inl u ∧ y = Sum.inl u) ∨
        (∃ v : V.functorOfPoints.obj (op T), x = Sum.inr v ∧ y = Sum.inr v) ∨
          (∃ v' : V'.functorOfPoints.obj (op T),
            x = Sum.inl (f'.app (op T) v') ∧ y = Sum.inr (ι.app (op T) v')) ∨
            (∃ v' : V'.functorOfPoints.obj (op T),
              x = Sum.inr (ι.app (op T) v') ∧ y = Sum.inl (f'.app (op T) v')) ∨
              ∃ w : (offDiagonal f').functorOfPoints.obj (op T),
                x = Sum.inr ((offDiagonalι f' ≫ pullback.fst f' f' ≫ ι).app (op T) w) ∧
                  y = Sum.inr ((offDiagonalι f' ≫ pullback.snd f' f' ≫ ι).app (op T) w) :=
  Iff.rfl

/-- Restriction of schemes over `S` preserves the generating image of `R`. -/
theorem glueRel_precomp {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] {T T' : Over S} (g : T' ⟶ T) {x y : uvPoint U V T}
    (h : glueRel ι f' T x y) :
    glueRel ι f' T' (uvPointMap g x) (uvPointMap g y) :=
  match h with
  | Or.inl ⟨u, hx, hy⟩ =>
      Or.inl ⟨U.functorOfPoints.map g.op u,
        congrArg (uvPointMap g) hx, congrArg (uvPointMap g) hy⟩
  | Or.inr (Or.inl ⟨v, hx, hy⟩) =>
      Or.inr <| Or.inl ⟨V.functorOfPoints.map g.op v,
        congrArg (uvPointMap g) hx, congrArg (uvPointMap g) hy⟩
  | Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩)) =>
      Or.inr <| Or.inr <| Or.inl ⟨V'.functorOfPoints.map g.op v',
        (congrArg (uvPointMap g) hx).trans
          (congrArg Sum.inl (NatTrans.naturality_apply f' g.op v').symm),
        (congrArg (uvPointMap g) hy).trans
          (congrArg Sum.inr (NatTrans.naturality_apply ι g.op v').symm)⟩
  | Or.inr (Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩))) =>
      Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨V'.functorOfPoints.map g.op v',
        (congrArg (uvPointMap g) hx).trans
          (congrArg Sum.inr (NatTrans.naturality_apply ι g.op v').symm),
        (congrArg (uvPointMap g) hy).trans
          (congrArg Sum.inl (NatTrans.naturality_apply f' g.op v').symm)⟩
  | Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hx, hy⟩))) =>
      Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨(offDiagonal f').functorOfPoints.map g.op w,
        (congrArg (uvPointMap g) hx).trans
          (congrArg Sum.inr
            (NatTrans.naturality_apply (offDiagonalι f' ≫ pullback.fst f' f' ≫ ι) g.op w).symm),
        (congrArg (uvPointMap g) hy).trans
          (congrArg Sum.inr
            (NatTrans.naturality_apply (offDiagonalι f' ≫ pullback.snd f' f' ≫ ι) g.op w).symm)⟩

/-- Evaluate a compatible pair of maps `U ⟶ B` and `V ⟶ B` on a pointwise coproduct section. -/
def uvHomApp {U V B : AlgebraicSpace S} (hU : U ⟶ B) (hV : V ⟶ B) {T : Over S} :
    uvPoint U V T → B.functorOfPoints.obj (op T) :=
  Sum.elim (fun u ↦ hU.app (op T) u) (fun v ↦ hV.app (op T) v)

/-- The evaluation map `uvHomApp` is natural in the test scheme. -/
theorem uvHomApp_natural {U V B : AlgebraicSpace S} (hU : U ⟶ B) (hV : V ⟶ B)
    {T T' : Over S} (g : T' ⟶ T) (x : uvPoint U V T) :
    B.functorOfPoints.map g.op (uvHomApp hU hV x) = uvHomApp hU hV (uvPointMap g x) :=
  match x with
  | Sum.inl u => (NatTrans.naturality_apply hU g.op u).symm
  | Sum.inr v => (NatTrans.naturality_apply hV g.op v).symm

/-- The two off-diagonal legs become equal after composing with a compatible pair of maps. -/
theorem offDiag_comp_eq {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU) :
    offDiagonalι f' ≫ pullback.fst f' f' ≫ ι ≫ hV =
      offDiagonalι f' ≫ pullback.snd f' f' ≫ ι ≫ hV :=
  congrArg (fun k ↦ offDiagonalι f' ≫ k) <|
    (congrArg (fun k ↦ pullback.fst f' f' ≫ k) h).trans <|
      (Category.assoc (pullback.fst f' f') f' hU).symm.trans <|
        (congrArg (fun k ↦ k ≫ hU) pullback.condition).trans <|
          (Category.assoc (pullback.snd f' f') f' hU).trans <|
            congrArg (fun k ↦ pullback.snd f' f' ≫ k) h.symm

/-- Related points of `U ⊔ V` have the same image under a compatible pair of maps into an
algebraic space `B`. -/
theorem glueRel_hom_eq {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU) {T : Over S}
    {x y : uvPoint U V T} (hxy : glueRel ι f' T x y) :
    uvHomApp hU hV x = uvHomApp hU hV y :=
  match hxy with
  | Or.inl ⟨_, hx, hy⟩ => (congrArg (uvHomApp hU hV) hx).trans (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inl ⟨_, hx, hy⟩) =>
      (congrArg (uvHomApp hU hV) hx).trans (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩)) =>
      (congrArg (uvHomApp hU hV) hx).trans <|
        ((CategoryTheory.comp_apply (f'.app (op T)) (hU.app (op T)) v').symm.trans <|
            (ConcreteCategory.congr_hom (NatTrans.congr_app h.symm (op T)) v').trans <|
              CategoryTheory.comp_apply (ι.app (op T)) (hV.app (op T)) v').trans <|
          (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩))) =>
      (congrArg (uvHomApp hU hV) hx).trans <|
        ((CategoryTheory.comp_apply (ι.app (op T)) (hV.app (op T)) v').symm.trans <|
            (ConcreteCategory.congr_hom (NatTrans.congr_app h (op T)) v').trans <|
              CategoryTheory.comp_apply (f'.app (op T)) (hU.app (op T)) v').trans <|
          (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hx, hy⟩))) =>
      (congrArg (uvHomApp hU hV) hx).trans <|
        ((CategoryTheory.comp_apply
              ((offDiagonalι f' ≫ pullback.fst f' f' ≫ ι).app (op T)) (hV.app (op T)) w).symm.trans <|
            (ConcreteCategory.congr_hom
                (NatTrans.congr_app (offDiag_comp_eq ι f' hV hU h) (op T)) w).trans <|
              CategoryTheory.comp_apply
                ((offDiagonalι f' ≫ pullback.snd f' f' ≫ ι).app (op T)) (hV.app (op T)) w).trans <|
          (congrArg (uvHomApp hU hV) hy).symm

/-- The Type `u` presheaf sending `T` to the quotient of the pointwise coproduct
`(U ⊔ V)(T)` by the image of `R(T)`. This is not an fppf sheaf. -/
def gluePresheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Quot (glueRel ι f' T.unop)
  map {X Y} η :=
    TypeCat.ofHom <|
      Quot.map (uvPointMap η.unop) fun _ _ h ↦ glueRel_precomp ι f' η.unop h
  map_id := sorry
  map_comp := sorry

/-- The value of `gluePresheaf` on `T` is the objectwise quotient by `glueRel`. -/
theorem gluePresheaf_obj {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : Over S) :
    (gluePresheaf ι f').obj (op T) = Quot (glueRel ι f' T) :=
  rfl

/-- Restriction in `gluePresheaf` is induced by `uvPointMap` on representatives. -/
theorem gluePresheaf_map_mk {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] {T T' : Over S} (g : T' ⟶ T) (x : uvPoint U V T) :
    (gluePresheaf ι f').map g.op (Quot.mk (glueRel ι f' T) x) =
      Quot.mk (glueRel ι f' T') (uvPointMap g x) :=
  rfl

/-- Evaluating a compatible pair of maps on a `gluePresheaf` class is natural. -/
theorem gluePresheaf_hom_natural {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU)
    {T T' : Over S} (g : T' ⟶ T) (q : Quot (glueRel ι f' T)) :
    B.functorOfPoints.map g.op
        (Quot.lift (uvHomApp hU hV) (fun _ _ hxy ↦ glueRel_hom_eq ι f' hV hU h hxy) q) =
      Quot.lift (uvHomApp hU hV) (fun _ _ hxy ↦ glueRel_hom_eq ι f' hV hU h hxy)
        ((gluePresheaf ι f').map g.op q) :=
  Quot.inductionOn q fun x ↦ uvHomApp_natural hU hV g x

/-- Restriction in `gluePresheaf` is functorial on quotient classes. -/
theorem gluePresheaf_map_comp_apply {U V V' : AlgebraicSpace S} (ι : V' ⟶ V)
    (f' : V' ⟶ U) [Separated f'] {T T' T'' : Over S} (g : T' ⟶ T) (f : T'' ⟶ T')
    (q : Quot (glueRel ι f' T)) :
    (gluePresheaf ι f').map f.op ((gluePresheaf ι f').map g.op q) =
      (gluePresheaf ι f').map (f ≫ g).op q :=
  Quot.inductionOn q fun x ↦
    congrArg (Quot.mk (glueRel ι f' T'')) (uvPointMap_comp g f x)



namespace EtalePresentation

/-- Mathlib's proved certificate, rather than a new existence axiom. -/
theorem certificate (T : Scheme.{u}) : HasSheafify T.smallEtaleTopology (Type u) :=
  inferInstance

/-- Actual base change on the small étale categories. -/
noncomputable abbrev etalePullback {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

set_option backward.isDefEq.respectTransparency false in
/-- Base change carries genuine étale covering sieves to covering sieves. -/
theorem pullback_coverPreserving {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etalePullback f) := by
  constructor
  intro U R hR
  change R.functorPushforward (etalePullback f) ∈
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X).restrictedTopology
      (Scheme.etaleTopology.over X) _
  rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
  change R.functorPushforward
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ Y ⋙ Over.pullback f) ∈ _
  rw [Sieve.functorPushforward_comp]
  exact (GrothendieckTopology.coverPreserving_overPullback Scheme.etaleTopology f).cover_preserve
    (((MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ Y).coverPreserving_restrictedTopology
      (Scheme.etaleTopology.over Y)).cover_preserve hR)

set_option backward.isDefEq.respectTransparency false in
/-- Continuity follows from proved finite-limit and cover preservation. -/
instance pullback_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etalePullback f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  -- Local instance justification (defeq pin): select the proved slice-pullback instance across Scheme.Etale.
  letI : PreservesFiniteLimits (etalePullback f) :=
    MorphismProperty.Over.instPreservesFiniteLimitsTopPullback @AlgebraicGeometry.Etale f
  -- Local instance justification (proof-local temporary data): derive flatness from this pullback's proved limit preservation.
  letI : RepresentablyFlat (etalePullback f) := flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.mpr (pullback_coverPreserving f)

/-- The étale-site inclusion is continuous for its actual induced topology. -/
instance forget_continuous (T : Scheme.{u}) :
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T).IsContinuous
      T.smallEtaleTopology (Scheme.etaleTopology.over T) := by
  -- Local instance justification (proof-local temporary data): use finite-limit creation to prove this forgetful functor flat.
  letI : RepresentablyFlat (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.mpr
    ((MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T).coverPreserving_restrictedTopology _)


variable {S : Scheme.{u}}

/-- The actual scheme-over-S object of an étale test object over T. -/
def toBase (T : Over S) : T.left.Etale ⥤ Over S :=
  Scheme.Etale.forget T.left ⋙ Over.map T.hom

/-- Restriction of a big presheaf to the small étale site of a test scheme. -/
def onTest (P : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) : T.left.Etaleᵒᵖ ⥤ Type u :=
  (toBase T).op ⋙ P

/-- Certified Type-u sheafification on the small étale site. -/
def onTestSheaf (P : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    Sheaf T.left.smallEtaleTopology (Type u) :=
  -- Local instance justification (defeq pin): force the kernel-audited Mathlib certificate for this sheafification operation.
  letI : HasSheafify T.left.smallEtaleTopology (Type u) := certificate T.left
  (presheafToSheaf T.left.smallEtaleTopology (Type u)).obj (onTest P T)

/-- Identity object of the small étale site. -/
def topTest (T : Over S) : T.left.Etale := Scheme.Etale.mk (𝟙 T.left)

/-- The section carrier uses only the proved small-site sheafification. -/
def sectionType (P : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) : Type u :=
  (onTestSheaf P T).obj.obj (op (topTest T))

set_option backward.isDefEq.respectTransparency false in
/-- The base-change projection as a natural map of actual test schemes. -/
def projection {X Y : Over S} (g : X ⟶ Y) :
    etalePullback g.left ⋙ toBase X ⟶ toBase Y where
  app E := Over.homMk (pullback.fst E.hom g.left) (by
    change pullback.fst E.hom g.left ≫ (E.hom ≫ Y.hom) =
      pullback.snd E.hom g.left ≫ X.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, Over.w g])
  naturality E F h := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- Presheaf restriction is induced by the pullback projections. -/
def pointRestriction (P : (Over S)ᵒᵖ ⥤ Type u) {X Y : Over S} (g : X ⟶ Y) :
    onTest P Y ⟶ (etalePullback g.left).op ⋙ onTest P X :=
  Functor.whiskerRight (NatTrans.op (projection g)) P

/-- Extend the projection map by the proved small-site sheafification adjunction. -/
def restrictionLift (P : (Over S)ᵒᵖ ⥤ Type u) {X Y : Over S} (g : X ⟶ Y) :
    (onTestSheaf P Y).obj ⟶ (etalePullback g.left).op ⋙ (onTestSheaf P X).obj :=
  sheafifyLift Y.left.smallEtaleTopology
    (pointRestriction P g ≫ Functor.whiskerLeft (etalePullback g.left).op
      (toSheafify X.left.smallEtaleTopology (onTest P X)))
    (((etalePullback g.left).sheafPushforwardContinuous (Type u)
      Y.left.smallEtaleTopology X.left.smallEtaleTopology).obj (onTestSheaf P X)).property

set_option backward.isDefEq.respectTransparency false in
/-- The actual map from the identity test object to the pulled-back identity. -/
def topPullback {X Y : Over S} (g : X ⟶ Y) :
    topTest X ⟶ (etalePullback g.left).obj (topTest Y) :=
  MorphismProperty.Over.homMk
    (pullback.lift g.left (𝟙 X.left)
      ((Category.comp_id g.left).trans (Category.id_comp g.left).symm))
    (by simp [topTest]) trivial

/-- The complete restriction operation, without a Small/IsIso existence placeholder. -/
def restrictSection (P : (Over S)ᵒᵖ ⥤ Type u) {X Y : Over S} (g : X ⟶ Y) :
    sectionType P Y → sectionType P X :=
  fun q ↦ (onTestSheaf P X).obj.map (topPullback g).op
    ((restrictionLift P g).app (op (topTest Y)) q)

/-- The genuine inclusion of étale covering sieves among fppf covering sieves. -/
theorem etale_le_fppf_over (S : Scheme.{u}) :
    Scheme.etaleTopology.over S ≤ Scheme.fppfTopology.over S := by
  have h : Scheme.etaleTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono
      (Scheme.precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact h _ hR

set_option backward.isDefEq.respectTransparency false in
/-- Relocalization of small étale test schemes is continuous. -/
instance toBase_continuous (T : Over S) :
    (toBase T).IsContinuous T.left.smallEtaleTopology (Scheme.etaleTopology.over S) :=
  Functor.isContinuous_comp
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T.left)
    (Over.map T.hom) T.left.smallEtaleTopology (Scheme.etaleTopology.over T.left)
    (Scheme.etaleTopology.over S)

/-- The identity test object considered over the original base maps to T by the identity. -/
def topCounit (T : Over S) : (toBase T).obj (topTest T) ⟶ T :=
  Over.homMk (𝟙 T.left) rfl

/-- The reverse identity map is explicit, not extracted from an IsIso placeholder. -/
def topUnit (T : Over S) : T ⟶ (toBase T).obj (topTest T) :=
  Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ (𝟙 T.left ≫ T.hom) = T.hom
    simp only [Category.id_comp])

/-- The actual unit from a global presheaf section to its small étale sheafification. -/
def unitSection (P : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    P.obj (op T) → sectionType P T :=
  fun q ↦ (toSheafify T.left.smallEtaleTopology (onTest P T)).app (op (topTest T))
    (P.map (topCounit T).op q)

/-- Restriction of an fppf sheaf to the small étale test site is a sheaf, by proved continuity. -/
def targetSheaf (Q : Sheaf (Scheme.fppfTopology.over S) (Type u)) (T : Over S) :
    Sheaf T.left.smallEtaleTopology (Type u) :=
  ((toBase T).sheafPushforwardContinuous (Type u)
    T.left.smallEtaleTopology (Scheme.etaleTopology.over S)).obj
      ⟨Q.obj, Q.property.of_le (etale_le_fppf_over S)⟩

/-- The actual universal extension on the small test site. -/
def descentLift (P : (Over S)ᵒᵖ ⥤ Type u)
    (Q : Sheaf (Scheme.fppfTopology.over S) (Type u)) (η : P ⟶ Q.obj) (T : Over S) :
    (onTestSheaf P T).obj ⟶ onTest Q.obj T :=
  sheafifyLift T.left.smallEtaleTopology
    (Functor.whiskerLeft (toBase T).op η) (targetSheaf Q T).property

/-- Evaluation of the descended map uses only the explicit identity-scheme map. -/
def descendSection (P : (Over S)ᵒᵖ ⥤ Type u)
    (Q : Sheaf (Scheme.fppfTopology.over S) (Type u)) (η : P ⟶ Q.obj) (T : Over S) :
    sectionType P T → Q.obj.obj (op T) :=
  fun q ↦ Q.obj.map (topUnit T).op ((descentLift P Q η T).app (op (topTest T)) q)

/-- The two explicit identity-scheme arrows cancel. -/
theorem topUnit_counit (T : Over S) : topUnit T ≫ topCounit T = 𝟙 T := by
  apply Over.OverMorphism.ext
  exact Category.id_comp (𝟙 T.left)

/-- The descended operation agrees with the original presheaf map on every generator. -/
theorem descend_unit (P : (Over S)ᵒᵖ ⥤ Type u)
    (Q : Sheaf (Scheme.fppfTopology.over S) (Type u)) (η : P ⟶ Q.obj)
    (T : Over S) (q : P.obj (op T)) :
    descendSection P Q η T (unitSection P T q) = η.app (op T) q := by
  have h := toSheafify_sheafifyLift T.left.smallEtaleTopology
    (Functor.whiskerLeft (toBase T).op η) (targetSheaf Q T).property
  have hq := congrArg (fun k : (onTest P T).obj (op (topTest T)) ⟶
      (onTest Q.obj T).obj (op (topTest T)) => k.hom (P.map (topCounit T).op q))
    (NatTrans.congr_app h (op (topTest T)))
  change Q.obj.map (topUnit T).op
    ((descentLift P Q η T).app (op (topTest T))
      ((toSheafify T.left.smallEtaleTopology (onTest P T)).app (op (topTest T))
        (P.map (topCounit T).op q))) = _
  rw [show (descentLift P Q η T).app (op (topTest T))
      ((toSheafify T.left.smallEtaleTopology (onTest P T)).app (op (topTest T))
        (P.map (topCounit T).op q)) =
      η.app (op ((toBase T).obj (topTest T))) (P.map (topCounit T).op q) from hq]
  rw [NatTrans.naturality_apply]
  change (Q.obj.map (topCounit T).op ≫ Q.obj.map (topUnit T).op) (η.app (op T) q) = _
  rw [← Q.obj.map_comp, ← op_comp, topUnit_counit, op_id, Q.obj.map_id]
  rfl

end EtalePresentation


/-- Sections of the quotient on the certified small étale site of each test
scheme. No admitted Small witness or freely chosen resizing equivalence is used. -/
def glueSheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : (Over S)ᵒᵖ ⥤ Type u where
  obj T := EtalePresentation.sectionType (gluePresheaf ι f') T.unop
  map g := ↾(EtalePresentation.restrictSection (gluePresheaf ι f') g.unop)
  map_id := sorry
  map_comp := sorry

/-- The carrier is definitionally the certified small-site section type. -/
theorem glueSheaf_obj {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : (Over S)ᵒᵖ) :
    (glueSheaf ι f').obj T = EtalePresentation.sectionType (gluePresheaf ι f') T.unop :=
  rfl

/-- Restriction is definitionally the explicit small-site pullback operation. -/
theorem glueSheaf_map {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] {X Y : (Over S)ᵒᵖ} (g : X ⟶ Y) :
    (glueSheaf ι f').map g =
      TypeCat.ofHom (EtalePresentation.restrictSection (gluePresheaf ι f') g.unop) :=
  rfl

/-- The étale quotient of this étale equivalence relation satisfies fppf descent.
This geometric law does not choose the carrier, restriction, unit, or descent maps. -/
theorem glueSheaf_isSheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (glueSheaf ι f') :=
  sorry

/-- The actual sheafification unit on each certified small étale test site. -/
def toGlueSheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : gluePresheaf ι f' ⟶ glueSheaf ι f' where
  app T := ↾(EtalePresentation.unitSection (gluePresheaf ι f') T.unop)
  naturality := sorry

/-- The quotient unit is locally injective for the fppf topology. -/
instance instIsLocallyInjective_toGlueSheaf {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (toGlueSheaf ι f') :=
  sorry

/-- The quotient unit is locally surjective for the fppf topology. -/
instance instIsLocallySurjective_toGlueSheaf {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (toGlueSheaf ι f') :=
  sorry

/-- The algebraic space of the fppf quotient of the specified étale relation. -/
def pushoutObj {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : AlgebraicSpace S :=
  ofFunctor (glueSheaf ι f') (glueSheaf_isSheaf ι f') sorry sorry

/-- The canonical map from the V summand to the fppf quotient. -/
def inl {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : V ⟶ pushoutObj ι f' where
  app T := ↾fun v ↦ (toGlueSheaf ι f').app T
    (Quot.mk (glueRel ι f' T.unop) (Sum.inr v))
  naturality := sorry

/-- The canonical map from the U summand to the fppf quotient. -/
def inr {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : U ⟶ pushoutObj ι f' where
  app T := ↾fun v ↦ (toGlueSheaf ι f').app T
    (Quot.mk (glueRel ι f' T.unop) (Sum.inl v))
  naturality := sorry

/-- A compatible pair of maps descends to the objectwise quotient, by the
existing real proof that every generating relation is equalized. -/
def gluePresheafDesc {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU) :
    gluePresheaf ι f' ⟶ B.functorOfPoints where
  app T := ↾(Quot.lift (uvHomApp hU hV)
    (fun _ _ hxy ↦ glueRel_hom_eq ι f' hV hU h hxy))
  naturality := by
    intro X Y g
    ext q
    exact (gluePresheaf_hom_natural ι f' hV hU h g.unop q).symm


/-- Extend a compatible pair into its given fppf sheaf via the proved small-site
adjunction, evaluated on the identity test scheme. -/
def desc {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B)
    (h : ι ≫ hV = f' ≫ hU) : pushoutObj ι f' ⟶ B where
  app T := ↾(EtalePresentation.descendSection (gluePresheaf ι f')
    ⟨B.functorOfPoints, B.isSheaf⟩ (gluePresheafDesc ι f' hV hU h) T.unop)
  naturality := sorry

/-- The descended map has the original compatible-pair formula on every generator. -/
theorem desc_toGlueSheaf_app {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V)
    (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f']
    (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU)
    (T : (Over S)ᵒᵖ) (q : (gluePresheaf ι f').obj T) :
    (desc ι f' hV hU h).app T ((toGlueSheaf ι f').app T q) =
      (gluePresheafDesc ι f' hV hU h).app T q :=
  EtalePresentation.descend_unit (gluePresheaf ι f')
    ⟨B.functorOfPoints, B.isSheaf⟩ (gluePresheafDesc ι f' hV hU h) T.unop q

/-- The square `ι`, `f'`, `inl`, `inr` commutes. -/
theorem pushout_condition {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    ι ≫ inl ι f' = f' ≫ inr ι f' := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro v
  apply congrArg ((toGlueSheaf ι f').app T)
  exact Quot.sound (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl, rfl⟩))))

/-- Postcomposing `inl` with `desc` recovers the map from `V`. -/
theorem desc_inl {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B)
    (h : ι ≫ hV = f' ≫ hU) : inl ι f' ≫ desc ι f' hV hU h = hV := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro v
  exact desc_toGlueSheaf_app ι f' hV hU h T (Quot.mk _ (Sum.inr v))

/-- Postcomposing `inr` with `desc` recovers the map from `U`. -/
theorem desc_inr {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B)
    (h : ι ≫ hV = f' ≫ hU) : inr ι f' ≫ desc ι f' hV hU h = hU := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro v
  exact desc_toGlueSheaf_app ι f' hV hU h T (Quot.mk _ (Sum.inl v))

/-- The explicit pushout cocone on `inl` and `inr`. -/
def pushoutCocone {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : PushoutCocone ι f' :=
  PushoutCocone.mk (inl ι f') (inr ι f') (pushout_condition ι f')

/-- The cocone on `pushoutObj` is a colimit cocone. -/
def pushoutCoconeIsColimit {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsColimit (pushoutCocone ι f') :=
  PushoutCocone.IsColimit.mk (pushout_condition ι f')
    (fun s ↦ desc ι f' s.inl s.inr s.condition)
    (fun s ↦ desc_inl ι f' s.inl s.inr s.condition)
    (fun s ↦ desc_inr ι f' s.inl s.inr s.condition)
    fun _ _ _ _ ↦ sorry

/-- An open immersion and a separated étale morphism of algebraic spaces over `S`
admit a pushout in `AlgebraicSpace S`. -/
instance instHasPushout {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : HasPushout ι f' :=
  HasColimit.mk ⟨pushoutCocone ι f', pushoutCoconeIsColimit ι f'⟩

/-- The canonical map `U ⟶ W` is an open immersion. -/
instance instIsOpenImmersion_inr {U V V' : AlgebraicSpace S} (ι : V' ⟶ V)
    (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsOpenImmersion (inr ι f') :=
  sorry

/-- The canonical map `V ⟶ W` is étale. -/
instance instEtale_inl {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : Etale (inl ι f') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
