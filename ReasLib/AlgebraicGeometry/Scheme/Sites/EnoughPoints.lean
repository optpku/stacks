/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Sites.Point.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Small

/-!
# Enough points for scheme sites

This module records enough-points results for the standard small, big, and
affine-over sites associated with a scheme.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v u' v' w

namespace AlgebraicGeometry.Scheme

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The geometric point obtained from the separable closure of a residue field. -/
private noncomputable def enoughPointsGeometricPoint (S : Scheme.{u}) (x : S) :
    Spec (.of (SeparableClosure (S.residueField x))) ⟶ S :=
  (SpecToEquivOfField (SeparableClosure (S.residueField x)) S).2
    ⟨x, CommRingCat.ofHom (algebraMap (S.residueField x) _)⟩

/-- A geometric point on the small Zariski site, with fibers in the required universe. -/
private noncomputable def liftedSmallZariskiPoint {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    GrothendieckTopology.Point.{u + 1} (smallZariskiTopology S) where
  fiber := smallZariskiForget S ⋙ coyoneda.obj (op (Over.mk s)) ⋙ uliftFunctor.{u + 1, u}
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective {X} R hR φ := by
    rcases φ with ⟨φ⟩
    obtain ⟨φ : Spec (.of Ω) ⟶ X.left, hφ, rfl⟩ := Over.homMk_surjective φ
    obtain ⟨𝒰, h, p, le⟩ := (mem_smallGrothendieckTopology _ _).1 hR
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (φ default)
    letI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨l, hl₁, hl₂⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) φ _ hy
    refine ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S,
      le _ _ ⟨i⟩, ⟨Over.homMk l (by simpa [← comp_over (𝒰.f i) S, ← Category.assoc, hl₁] using hφ)⟩, ?_⟩
    apply ULift.ext
    apply Over.OverMorphism.ext
    exact hl₁

private theorem liftedSmallZariskiPoints_isConservative (S : Scheme.{u}) :
    (ObjectProperty.ofObj (fun x : S ↦
      liftedSmallZariskiPoint (enoughPointsGeometricPoint S x))).IsConservativeFamilyOfPoints := by
  let s := enoughPointsGeometricPoint S
  let p (x : S) := liftedSmallZariskiPoint (s x)
  change (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints
  refine .mk' ?_
  intro X R hR
  change R ∈ S.smallGrothendieckTopology IsOpenImmersion X
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    mem_toGrothendieck_smallPretopology]
  intro x
  letI : IsOpenImmersion X.hom := X.prop
  let X' : S.Etale := X.left.asOverProp S (show Etale X.hom from inferInstance)
  have hs : s (X.hom x) default = X.hom x := by simp [s, enoughPointsGeometricPoint, SpecToEquivOfField]
  obtain ⟨x', hx'⟩ := pointSmallEtaleFiberObjToPreimage_surjective
    (s (X.hom x)) hs X' ⟨x, rfl⟩
  let z := (default : Spec (.of (SeparableClosure (S.residueField (X.hom x)))))
  have hx : x'.left z = x := congrArg Subtype.val hx'
  obtain ⟨Y, g, hg, y, heq⟩ := hR ⟨_, ⟨X.hom x⟩⟩ (ULift.up x')
  letI : IsOpenImmersion Y.hom := Y.prop
  letI : IsOpenImmersion (g.left ≫ X.hom) := by
    have hw : g.left ≫ X.hom = Y.hom := g.w
    exact hw.symm ▸ Y.prop
  refine ⟨Y, g, y.down.left z, hg, IsOpenImmersion.of_comp g.left X.hom, ?_⟩
  have heq' := congrArg (fun t ↦ t.down.left z) heq
  exact heq'.trans hx

/-- Lift the fibers of mathlib's geometric étale point without changing its neighborhood data. -/
private noncomputable def liftedSmallEtalePoint {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    GrothendieckTopology.Point.{u + 1} (smallEtaleTopology S) where
  fiber := (pointSmallEtale s).fiber ⋙ uliftFunctor.{u + 1, u}
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨Y, f, hf, y, hy⟩ := (pointSmallEtale s).jointly_surjective R hR x.down
    exact ⟨Y, f, hf, ⟨y⟩, ULift.ext _ _ hy⟩

private theorem liftedSmallEtalePoints_isConservative (S : Scheme.{u}) :
    (ObjectProperty.ofObj (fun x : S ↦
      liftedSmallEtalePoint (enoughPointsGeometricPoint S x))).IsConservativeFamilyOfPoints := by
  let s := enoughPointsGeometricPoint S
  let p (x : S) := liftedSmallEtalePoint (s x)
  change (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints
  refine .mk' ?_
  intro X R hR
  obtain ⟨α, T, f, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  have hs : s (X.hom x) default = X.hom x := by simp [s, enoughPointsGeometricPoint, SpecToEquivOfField]
  obtain ⟨x', hx'⟩ := pointSmallEtaleFiberObjToPreimage_surjective
    (s (X.hom x)) hs X ⟨x, rfl⟩
  let z := (default : Spec (.of (SeparableClosure (S.residueField (X.hom x)))))
  have hx : x'.left z = x := congrArg Subtype.val hx'
  obtain ⟨W, g, ⟨Z, q, _, ⟨a⟩, rfl⟩, y, heq⟩ := hR ⟨_, ⟨X.hom x⟩⟩ (ULift.up x')
  refine ⟨a, q.left (y.down.left z), ?_⟩
  have heq' := congrArg (fun t ↦ t.down.left z) heq
  exact heq'.trans hx

/-- Restrict a conservative family to a small full dense subsite. -/
private theorem hasEnoughPoints_of_denseSubsite
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.IsDenseSubsite J K] [EssentiallySmall.{w} C]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [K.WEqualsLocallyBijective (Type w)]
    [GrothendieckTopology.HasEnoughPoints.{w} K] :
    GrothendieckTopology.HasEnoughPoints.{w} J := by
  haveI : F.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K F
  have hcofiltered (p : GrothendieckTopology.Point.{w} K) :
      IsCofiltered (F ⋙ p.fiber).Elements := by
    let e := Functor.Elements.precomp F p.fiber
    haveI : e.Full := ⟨by
      intro X Y f
      refine ⟨⟨F.preimage f.1, ?_⟩, ?_⟩
      · simpa [e] using f.2
      · apply Subtype.ext
        exact F.map_preimage f.1⟩
    haveI : e.Faithful := ⟨by
      intro X Y f g h
      apply Subtype.ext
      exact F.map_injective (congrArg Subtype.val h)⟩
    refine IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful e ?_
    rintro ⟨Y, y⟩
    obtain ⟨Z, g, ⟨⟨X, a, b, hab⟩⟩, z, hz⟩ :=
      p.jointly_surjective _ (F.is_cover_of_isCoverDense K Y) y
    refine ⟨⟨X, p.fiber.map a z⟩, ⟨⟨b, ?_⟩⟩⟩
    change p.fiber.map b (p.fiber.map a z) = y
    rw [← comp_apply, ← p.fiber.map_comp, hab]
    exact hz
  let q (p : GrothendieckTopology.Point.{w} K) : GrothendieckTopology.Point.{w} J :=
    { fiber := F ⋙ p.fiber
      isCofiltered := hcofiltered p
      initiallySmall := initiallySmall_of_essentiallySmall _
      jointly_surjective := by
        intro X R hR x
        obtain ⟨Y, f, ⟨W, g, h, hg, rfl⟩, y, rfl⟩ :=
          p.jointly_surjective _
            ((Functor.IsDenseSubsite.coverPreserving J K F).cover_preserve hR) x
        exact ⟨W, g, hg, p.fiber.map h y, by simp⟩ }
  obtain ⟨P, hsmall, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty K
  letI := hsmall
  let p (x : P.FullSubcategory) := q x.obj
  refine ⟨ObjectProperty.ofObj p, inferInstance, .mk' ?_⟩
  intro X R hR
  obtain ⟨α, T, f, rfl⟩ := R.exists_eq_ofArrows
  apply (Functor.IsDenseSubsite.functorPushforward_mem_iff (G := F) (J := J) (K := K)).mp
  rw [Sieve.functorPushforward_ofArrows]
  apply (hP.jointly_reflect_ofArrows_mem_of_small (fun i ↦ F.map (f i))).2
  intro Φ x
  obtain ⟨W, g, ⟨Z, a, _, ⟨i⟩, rfl⟩, y, heq⟩ := hR ⟨_, ⟨Φ⟩⟩ x
  refine ⟨i, Φ.obj.fiber.map (F.map a) y, ?_⟩
  dsimp [p, q] at heq
  simpa only [Functor.map_comp, comp_apply] using heq

/-- Affine covers make the affine inclusion dense for every topology containing Zariski. -/
private theorem hasEnoughPoints_affineOver_of_le (S : Scheme.{u})
    (K : GrothendieckTopology (Over S)) (hK : zariskiTopology.over S ≤ K)
    [GrothendieckTopology.HasEnoughPoints.{u + 1} K] :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (affineOverTopology S K) := by
  haveI : (AffineOver.forget S).IsCoverDense K := ⟨by
    intro X
    apply hK
    rw [mem_overGrothendieckTopology]
    let 𝒰 := X.left.affineCover
    letI (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ X.hom⟩
    letI : 𝒰.Over S := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance, ?_⟩
    rintro Y f ⟨i⟩
    refine ⟨⟨AffineOver.mk (𝒰.X i) inferInstance (𝒰.f i ≫ X.hom),
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (𝒰.f i ≫ X.hom) = 𝒰.X i ↘ S
        rw [Category.id_comp]
        rfl), Over.homMk (𝒰.f i) rfl, ?_⟩⟩
    ext
    simp⟩
  haveI : (AffineOver.forget S).IsDenseSubsite (affineOverTopology S K) K := by
    change (AffineOver.forget S).IsDenseSubsite
      ((AffineOver.forget S).restrictedTopology K) K
    infer_instance
  exact hasEnoughPoints_of_denseSubsite (affineOverTopology S K) K (AffineOver.forget S)

/-- Points on all small sites over objects of a big site jointly detect isomorphisms. -/
private theorem hasEnoughPoints_over_of_small
    (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.RespectsIso]
    (p : ∀ T : Scheme.{u}, T → GrothendieckTopology.Point.{u + 1}
      (T.smallGrothendieckTopology (Q := P) P))
    (hp : ∀ T, (ObjectProperty.ofObj (p T)).IsConservativeFamilyOfPoints)
    (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (S.overGrothendieckTopology P) := by
  let K := S.overGrothendieckTopology P
  haveI (T : Scheme.{u}) :
      (MorphismProperty.Over.forget P ⊤ T).IsContinuous
        (T.smallGrothendieckTopology (Q := P) P) (T.overGrothendieckTopology P) :=
    by
      letI : RepresentablyFlat (MorphismProperty.Over.forget P ⊤ T) :=
        flat_of_preservesFiniteLimits _
      exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
        ((MorphismProperty.Over.forget P ⊤ T).coverPreserving_restrictedTopology _)
  let F (T : Over S) := MorphismProperty.Over.forget P ⊤ T.left ⋙ Over.map T.hom
  haveI (T : Over S) : (F T).IsContinuous (T.left.smallGrothendieckTopology (Q := P) P) K :=
    Functor.isContinuous_comp (MorphismProperty.Over.forget P ⊤ T.left) (Over.map T.hom)
      (T.left.smallGrothendieckTopology (Q := P) P) (T.left.overGrothendieckTopology P) K
  haveI (T : Over S) : (F T).IsCocontinuous (T.left.smallGrothendieckTopology (Q := P) P) K :=
    isCocontinuous_comp (MorphismProperty.Over.forget P ⊤ T.left) (Over.map T.hom)
      (T.left.smallGrothendieckTopology (Q := P) P) (T.left.overGrothendieckTopology P)
  let q (i : Σ T : Over S, T.left) := (p i.1.left i.2).map (F i.1) K
  refine ⟨ObjectProperty.ofObj q, inferInstance, ⟨⟨?_⟩⟩⟩
  intro A B f hf
  have hrestrict (T : Over S) :
      IsIso ((F T).sheafPushforwardContinuous (Type (u + 1))
        (T.left.smallGrothendieckTopology (Q := P) P) K |>.map f) := by
    letI (Φ : (ObjectProperty.ofObj (p T.left)).FullSubcategory) :
        IsIso (Φ.obj.sheafFiber.map
          ((F T).sheafPushforwardContinuous (Type (u + 1))
            (T.left.smallGrothendieckTopology (Q := P) P) K |>.map f)) := by
      rcases Φ with ⟨_, ⟨x⟩⟩
      letI := hf ⟨_, ⟨⟨T, x⟩⟩⟩
      exact ((MorphismProperty.isomorphisms (Type (u + 1))).arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso
          ((p T.left x).sheafFiberMapIso (F T) K (Type (u + 1)))).app
            (Arrow.mk f))).1 (inferInstanceAs (IsIso ((q ⟨T, x⟩).sheafFiber.map f)))
    exact (hp T.left).jointlyReflectIsomorphisms_type.isIso _
  haveI (T : Over S) : IsIso (f.hom.app (op T)) := by
    let X : P.Over ⊤ T.left := MorphismProperty.Over.mk ⊤ (𝟙 T.left) (P.id_mem _)
    letI := hrestrict T
    haveI : IsIso (((F T).sheafPushforwardContinuous (Type (u + 1))
        (T.left.smallGrothendieckTopology (Q := P) P) K).map f).hom := by
      change IsIso ((sheafToPresheaf _ _).map
        (((F T).sheafPushforwardContinuous (Type (u + 1))
          (T.left.smallGrothendieckTopology (Q := P) P) K).map f))
      infer_instance
    have ht : IsIso ((((F T).sheafPushforwardContinuous (Type (u + 1))
      (T.left.smallGrothendieckTopology (Q := P) P) K).map f).hom.app (op X)) :=
      inferInstance
    have hobj : (F T).obj X = T := by
      change Over.mk (𝟙 T.left ≫ T.hom) = T
      rw [Category.id_comp]
      rfl
    change IsIso (f.hom.app (op ((F T).obj X))) at ht
    exact hobj ▸ ht
  have hhom : IsIso f.hom := (NatTrans.isIso_iff_isIso_app _).2 (fun T ↦ inferInstance)
  letI : IsIso ((sheafToPresheaf K (Type (u + 1))).map f) := hhom
  exact isIso_of_reflects_iso f (sheafToPresheaf K (Type (u + 1)))

end

/-- The small affine Zariski site of a scheme has enough points. -/
instance hasEnoughPoints_smallAffineZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (smallAffineZariskiTopology S) :=
  sorry

/-- The small Zariski site of a scheme has enough points. -/
instance hasEnoughPoints_smallZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (smallZariskiTopology S) :=
  ⟨_, inferInstance, liftedSmallZariskiPoints_isConservative S⟩

/-- The small affine étale site of a scheme has enough points. -/
instance hasEnoughPoints_smallAffineEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (AffineEtale.topology S) := by
  letI : GrothendieckTopology.HasEnoughPoints.{u + 1} (smallEtaleTopology S) :=
    ⟨_, inferInstance, liftedSmallEtalePoints_isConservative S⟩
  exact hasEnoughPoints_of_denseSubsite (AffineEtale.topology S) (smallEtaleTopology S)
    (AffineEtale.Spec S)

/-- The small étale site of a scheme has enough points. -/
theorem hasEnoughPoints_smallEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S) :=
  inferInstance

/-- The big Zariski site over a scheme has enough points. -/
instance hasEnoughPoints_bigZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (zariskiTopology.over S) :=
  hasEnoughPoints_over_of_small IsOpenImmersion
    (fun T x ↦ liftedSmallZariskiPoint (enoughPointsGeometricPoint T x))
    liftedSmallZariskiPoints_isConservative S

/-- The affine-over Zariski site of a scheme has enough points. -/
instance hasEnoughPoints_affineZariski (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (zariskiTopology.over S)) :=
  hasEnoughPoints_affineOver_of_le S _ le_rfl

/-- The big étale site over a scheme has enough points. -/
instance hasEnoughPoints_bigEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology (@Etale)) :=
  hasEnoughPoints_over_of_small (@Etale)
    (fun T x ↦ liftedSmallEtalePoint (enoughPointsGeometricPoint T x))
    liftedSmallEtalePoints_isConservative S

/-- The affine-over étale site of a scheme has enough points. -/
instance hasEnoughPoints_affineEtale (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (S.overGrothendieckTopology (@Etale))) :=
  hasEnoughPoints_affineOver_of_le S _ (by
    intro X R hR
    exact (grothendieckTopology_monotone
      (show (@IsOpenImmersion : MorphismProperty Scheme.{u}) ≤ @Etale from
        fun _ _ f hf ↦ by letI := hf; infer_instance)) _ hR)

/-- The big smooth site over a scheme has enough points. -/
instance hasEnoughPoints_bigSmooth (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology (@Smooth)) :=
  sorry

/-- The affine-over smooth site of a scheme has enough points. -/
instance hasEnoughPoints_affineSmooth (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (S.overGrothendieckTopology (@Smooth))) :=
  hasEnoughPoints_affineOver_of_le S _ (by
    intro X R hR
    exact (grothendieckTopology_monotone
      (show (@IsOpenImmersion : MorphismProperty Scheme.{u}) ≤ @Smooth from
        fun _ _ f hf ↦ by letI := hf; infer_instance)) _ hR)

/-- The big syntomic site over a scheme has enough points. -/
instance hasEnoughPoints_bigSyntomic (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology (@Syntomic)) :=
  sorry

/-- The affine-over syntomic site of a scheme has enough points. -/
instance hasEnoughPoints_affineSyntomic (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (S.overGrothendieckTopology (@Syntomic))) :=
  sorry

/-- The big fppf site over a scheme has enough points. -/
instance hasEnoughPoints_bigFppf (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (fppfTopology.over S) :=
  sorry

/-- The affine-over fppf site of a scheme has enough points. -/
instance hasEnoughPoints_affineFppf (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (affineOverTopology S (fppfTopology.over S)) :=
  hasEnoughPoints_affineOver_of_le S _ (by
    intro X R hR
    exact (Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage) _ hR)

end AlgebraicGeometry.Scheme
