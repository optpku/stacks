module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Left Derived Functors from a Good Subset

This leaf is the left-derived dual of the corresponding right-subset criterion. A
denominator-cofinal object property on which a functor inverts the relevant denominators supplies
left-derived computation and source-definedness everywhere without choosing a particular
derived-category model. The weaker Mathlib pointwise-existence consequence remains available
separately.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open MorphismProperty Limits

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.IsSaturatedMultiplicativeSystem]

private theorem mem_of_isIso_map {X Y : D} (f : X ⟶ Y)
    (h : IsIso (S.Q.map f)) : S f := by
  have hs := (saturation.mem_iff S f).mpr h
  exact (congrArg (fun W : MorphismProperty D => W f)
    (IsSaturatedMultiplicativeSystem.saturation_eq S)).mp hs

private theorem exists_goodFraction
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    {X Y : D} (a : S.Q.obj X ⟶ S.Q.obj Y) :
    ∃ f : S.RightFraction X Y, P f.X' ∧ a = f.map S.Q (Localization.inverts S.Q S) := by
  obtain ⟨f, hf⟩ := Localization.exists_rightFraction S.Q S a
  obtain ⟨Z, t, hZ, ht⟩ := hP f.X'
  let g : S.RightFraction X Y := ⟨t ≫ f.s, S.comp_mem _ _ ht f.hs, t ≫ f.f⟩
  refine ⟨g, hZ, ?_⟩
  have := Localization.inverts S.Q S g.s g.hs
  apply (cancel_epi (S.Q.map g.s)).mp
  rw [g.map_s_comp_map]
  change S.Q.map (t ≫ f.s) ≫ a = S.Q.map (t ≫ f.f)
  rw [hf, Functor.map_comp, Functor.map_comp, Category.assoc, f.map_s_comp_map]

private theorem goodFraction_eq
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X Y : D} (hX : P X) (f g : S.RightFraction X Y)
    (hf : P f.X') (hg : P g.X')
    (h : f.map S.Q (Localization.inverts S.Q S) =
      g.map S.Q (Localization.inverts S.Q S)) :
    (@asIso _ _ _ _ (F.map f.s) (hF f.s hf hX f.hs)).inv ≫ F.map f.f =
      (@asIso _ _ _ _ (F.map g.s) (hF g.s hg hX g.hs)).inv ≫ F.map g.f := by
  obtain ⟨Z, t, r, hs, hfg, ht⟩ := (RightFraction.map_eq_iff S.Q S f g).mp h
  obtain ⟨T, q, hT, hq⟩ := hP Z
  have hqt : S (q ≫ t) := by
    apply mem_of_isIso_map S
    have hcomp := Localization.inverts S.Q S (q ≫ (t ≫ f.s)) (S.comp_mem _ _ hq ht)
    have := Localization.inverts S.Q S f.s f.hs
    rw [← Category.assoc, Functor.map_comp] at hcomp
    exact (isIso_comp_right_iff (S.Q.map (q ≫ t)) (S.Q.map f.s)).mp hcomp
  have hqr : S (q ≫ r) := by
    apply mem_of_isIso_map S
    have hcomp := Localization.inverts S.Q S (q ≫ (r ≫ g.s))
      (S.comp_mem _ _ hq (hs ▸ ht))
    have := Localization.inverts S.Q S g.s g.hs
    rw [← Category.assoc, Functor.map_comp] at hcomp
    exact (isIso_comp_right_iff (S.Q.map (q ≫ r)) (S.Q.map g.s)).mp hcomp
  have := hF (q ≫ t) hT hf hqt
  have := hF (q ≫ r) hT hg hqr
  have := hF f.s hf hX f.hs
  have := hF g.s hg hX g.hs
  apply (cancel_epi (F.map (q ≫ t) ≫ F.map f.s)).mp
  have hs' : F.map (q ≫ t) ≫ F.map f.s = F.map (q ≫ r) ≫ F.map g.s := by
    simp only [← F.map_comp, Category.assoc, hs]
  simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc (F.map (q ≫ t)) (F.map f.s), hs']
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  simp only [← F.map_comp, Category.assoc, hfg]

private noncomputable def goodValueMap
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X Y : D} (hX : P X) (a : S.Q.obj X ⟶ S.Q.obj Y) : F.obj X ⟶ F.obj Y :=
  let f := (exists_goodFraction S P hP a).choose
  let hf := (exists_goodFraction S P hP a).choose_spec.1
  (@asIso _ _ _ _ (F.map f.s) (hF f.s hf hX f.hs)).inv ≫ F.map f.f

private theorem goodValueMap_eq
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X Y : D} (hX : P X) (a : S.Q.obj X ⟶ S.Q.obj Y)
    (f : S.RightFraction X Y) (hf : P f.X')
    (ha : a = f.map S.Q (Localization.inverts S.Q S)) :
    goodValueMap F S P hP hF hX a =
      (@asIso _ _ _ _ (F.map f.s) (hF f.s hf hX f.hs)).inv ≫ F.map f.f :=
  goodFraction_eq F S P hP hF hX _ f
    (exists_goodFraction S P hP a).choose_spec.1 hf
    ((exists_goodFraction S P hP a).choose_spec.2.symm.trans ha)

private theorem goodValueMap_map
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X Y : D} (hX : P X) (f : X ⟶ Y) :
    goodValueMap F S P hP hF hX (S.Q.map f) = F.map f := by
  rw [goodValueMap_eq F S P hP hF hX _ (RightFraction.ofHom S f) hX
    (RightFraction.map_ofHom S f S.Q (Localization.inverts S.Q S)).symm]
  simp [RightFraction.ofHom, F.map_id]

private theorem goodValueMap_comp_map
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X Y Z : D} (hX : P X) (a : S.Q.obj X ⟶ S.Q.obj Y) (f : Y ⟶ Z) :
    goodValueMap F S P hP hF hX (a ≫ S.Q.map f) =
      goodValueMap F S P hP hF hX a ≫ F.map f := by
  obtain ⟨g, hg, ha⟩ := exists_goodFraction S P hP a
  let g' : S.RightFraction X Z := ⟨g.s, g.hs, g.f ≫ f⟩
  have ha' : a ≫ S.Q.map f = g'.map S.Q (Localization.inverts S.Q S) := by
    rw [ha]
    simp [RightFraction.map, g', Functor.map_comp, Category.assoc]
  rw [goodValueMap_eq F S P hP hF hX _ g' hg ha',
    goodValueMap_eq F S P hP hF hX _ g hg ha]
  simp [g', Functor.map_comp, Category.assoc]

private noncomputable def goodCone
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X T : D} (hT : P T) (e : S.Q.obj T ≅ S.Q.obj X) :
    Cone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) where
  pt := F.obj T
  π :=
    { app j := goodValueMap F S P hP hF hT (e.hom ≫ j.hom)
      naturality j k f := by
        change 𝟙 _ ≫ goodValueMap F S P hP hF hT (e.hom ≫ k.hom) =
          goodValueMap F S P hP hF hT (e.hom ≫ j.hom) ≫ F.map f.right
        rw [Category.id_comp, ← goodValueMap_comp_map F S P hP hF hT,
          Category.assoc, StructuredArrow.w] }

private theorem goodCone_leg
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X T : D} (hT : P T) (e : S.Q.obj T ≅ S.Q.obj X) :
    (goodCone F S P hP hF hT e).π.app (StructuredArrow.mk e.inv) = 𝟙 _ := by
  change goodValueMap F S P hP hF hT (e.hom ≫ e.inv) = 𝟙 _
  rw [e.hom_inv_id, ← S.Q.map_id, goodValueMap_map F S P hP hF hT, F.map_id]

private theorem goodCone_isEssentiallyConstant
    (P : ObjectProperty D)
    (hP : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hF : ∀ {X Y : D} (s : X ⟶ Y), P X → P Y → S s → IsIso (F.map s))
    {X T : D} (hT : P T) (e : S.Q.obj T ≅ S.Q.obj X) :
    (goodCone F S P hP hF hT e).IsEssentiallyConstant := by
  refine ⟨StructuredArrow.mk e.inv, ⟨𝟙 _, ?_⟩, ?_⟩
  · rw [goodCone_leg F S P hP hF hT e]
    exact Category.id_comp _
  · intro j
    obtain ⟨f, hf, ha⟩ := exists_goodFraction S P hP (e.hom ≫ j.hom)
    have := Localization.inverts S.Q S f.s f.hs
    let k := StructuredArrow.mk (e.inv ≫ CategoryTheory.inv (S.Q.map f.s))
    have hki : k.hom ≫ S.Q.map f.s = e.inv := by simp [k]
    have hkj : k.hom ≫ S.Q.map f.f = j.hom := by
      dsimp [k]
      rw [Category.assoc]
      change e.inv ≫ f.map S.Q (Localization.inverts S.Q S) = j.hom
      rw [← ha]
      simp
    refine ⟨k, StructuredArrow.homMk f.s hki,
      StructuredArrow.homMk f.f hkj, ?_⟩
    change F.map f.f = F.map f.s ≫ 𝟙 _ ≫
      goodValueMap F S P hP hF hT (e.hom ≫ j.hom)
    rw [goodValueMap_eq F S P hP hF hT _ f hf ha]
    have := hF f.s hf hT f.hs
    simp

/-- An object in a denominator-cofinal good subset computes the pointwise
left-derived value when `F` inverts denominators between good objects. -/
@[stacks 06XN, stacks 0FTF "good objects compute a left-derived functor"]
theorem LeftDerived.ComputesAt.of_mem_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    {X : D} (hX : P X) :
    LeftDerived.ComputesAt F S X := by
  let c := goodCone F S P hP_reaches hP_isIso hX (Iso.refl (S.Q.obj X))
  have hc := goodCone_isEssentiallyConstant F S P hP_reaches hP_isIso hX
    (Iso.refl (S.Q.obj X))
  have hDefined : LeftDerived.DefinedAt F S X := ⟨⟨c, hc⟩⟩
  refine { toDefinedAt := hDefined, isIso_valueProjection := ?_ }
  let e : limit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) ≅ F.obj X :=
    (limit.isLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)).conePointUniqueUpToIso
    hc.isLimit
  have he : e.hom = LeftDerived.Value.π F S (𝟙 X) (S.id_mem X) := by
    have h := (limit.isLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)).conePointUniqueUpToIso_hom_comp
      hc.isLimit (StructuredArrow.mk (𝟙 (S.Q.obj X)))
    change e.hom ≫ goodValueMap F S P hP_reaches hP_isIso hX
        (𝟙 (S.Q.obj X) ≫ 𝟙 (S.Q.obj X)) =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
        (StructuredArrow.mk (𝟙 (S.Q.obj X))) at h
    rw [Category.id_comp, ← S.Q.map_id, goodValueMap_map F S P hP_reaches hP_isIso hX,
      F.map_id, Category.comp_id] at h
    have hi : (Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv =
        S.Q.map (𝟙 X) := by
      apply Iso.inv_ext
      change S.Q.map (𝟙 X) ≫ S.Q.map (𝟙 X) = 𝟙 _
      rw [Functor.map_id, Category.id_comp]
    change e.hom = limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
      (StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv))
    rw [hi]
    exact h
  rw [← he]
  exact e.isIso_hom

/-- A denominator-cofinal object property on which the functor inverts internal
denominators makes the left-derived functor source-defined everywhere. -/
@[stacks 06XN, stacks 0FTF "cofinal good objects define a left-derived functor"]
theorem LeftDerived.EverywhereDefined.of_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    Functor.LeftDerived.EverywhereDefined F S := by
  constructor
  intro X
  obtain ⟨T, s, hT, hs⟩ := hP_reaches X
  exact ⟨⟨goodCone F S P hP_reaches hP_isIso hT (Localization.isoOfHom S.Q S s hs),
    goodCone_isEssentiallyConstant F S P hP_reaches hP_isIso hT
      (Localization.isoOfHom S.Q S s hs)⟩⟩

/-- A denominator-cofinal object property on which `F` inverts denominators
supplies pointwise left-derived values at every object. -/
@[stacks 06XN]
theorem LeftDerived.EverywhereDefined.hasPointwise_of_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor S :=
  @LeftDerived.EverywhereDefined.hasPointwise _ _ _ _ F S
    (LeftDerived.EverywhereDefined.of_subset F S P hP_reaches hP_isIso)

/-- A denominator-cofinal object property on which `F` inverts internal
denominators supplies a total left-derived functor. This is an ordinary theorem rather than a
proof-dependent instance, so a caller can install the result only where a concrete derived
construction needs it. -/
@[stacks 06XN]
theorem LeftDerived.EverywhereDefined.hasFunctor_of_subset
    (P : ObjectProperty D)
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    F.HasLeftDerivedFunctor S :=
  @Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _ _ _ F S
    (LeftDerived.EverywhereDefined.hasPointwise_of_subset F S P hP_reaches hP_isIso)

/-- An object in a full subcategory admitting left resolutions computes its
left-derived value when the restricted denominator system is inverted by `P.ι ⋙ F`. -/
@[stacks 06XN "left-derived computation from a full subcategory"]
theorem LeftDerived.ComputesAt.of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F))
    {X : D} (hX : P X) :
    LeftDerived.ComputesAt F S X := by
  apply LeftDerived.ComputesAt.of_mem_subset F S P
  · intro Y
    obtain ⟨r⟩ := (show (fullSubcategoryLocalizerMorphism P S).HasLeftResolutions from
      inferInstance) Y
    exact ⟨r.X₁.obj, r.w, r.X₁.property, r.hw⟩
  · intro Y Y' f hY hY' hf
    exact hF (ObjectProperty.homMk (X := ⟨Y, hY⟩) (Y := ⟨Y', hY'⟩) f) hf
  · exact hX

/-- Left resolutions by a full subcategory on which `P.ι ⋙ F` inverts the
restricted denominators make the left-derived functor source-defined everywhere. -/
@[stacks 06XN "left-derived source-definedness from a full subcategory"]
theorem LeftDerived.EverywhereDefined.of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    Functor.LeftDerived.EverywhereDefined F S := by
  apply LeftDerived.EverywhereDefined.of_subset F S P
  · intro Y
    obtain ⟨r⟩ := (show (fullSubcategoryLocalizerMorphism P S).HasLeftResolutions from
      inferInstance) Y
    exact ⟨r.X₁.obj, r.w, r.X₁.property, r.hw⟩
  · intro Y Y' f hY hY' hf
    exact hF (ObjectProperty.homMk (X := ⟨Y, hY⟩) (Y := ⟨Y', hY'⟩) f) hf

/-- Left resolutions by a full subcategory on which the restricted functor
inverts denominators supply pointwise left-derived values at every object. -/
@[stacks 06XN "pointwise left-derived existence from a full subcategory"]
theorem LeftDerived.EverywhereDefined.hasPointwise_of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    F.HasPointwiseLeftDerivedFunctor S :=
  @LeftDerived.EverywhereDefined.hasPointwise _ _ _ _ F S
    (LeftDerived.EverywhereDefined.of_fullSubcategory F S P hF)

/-- Left resolutions by a full subcategory on which the restricted functor
inverts denominators supply a total left-derived functor. -/
@[stacks 06XN "total left-derived functor from a full subcategory"]
theorem LeftDerived.EverywhereDefined.hasFunctor_of_fullSubcategory
    (P : ObjectProperty D)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F)) :
    F.HasLeftDerivedFunctor S :=
  @Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _ _ _ F S
    (LeftDerived.EverywhereDefined.hasPointwise_of_fullSubcategory F S P hF)


end CategoryTheory.Functor
