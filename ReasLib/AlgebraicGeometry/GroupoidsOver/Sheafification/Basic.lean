/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedTopology

/-!
# Sheafification in a prescribed universe

Small local sites certify section sizes; explicit additive equivalences then transport
the sheafification adjunction to the original universe. Slice topology comparisons
use the Cartesian lifts of a given groupoid fibration.
-/

/-! ## DenseSiteComposition -/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.GroupoidsOver.Sheafification

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]

/-- Cover density composes when the outer functor preserves covering sieves. -/
theorem coverDense_comp (G : A ⥤ B) (F : B ⥤ C)
    (J : GrothendieckTopology B) (K : GrothendieckTopology C)
    [G.IsCoverDense J] [F.IsCoverDense K] (hF : CoverPreserving J K F) :
    (G ⋙ F).IsCoverDense K where
  is_cover X := by
    apply K.transitive (F.is_cover_of_isCoverDense K X)
    rintro W k ⟨⟨Y, a, b, fac⟩⟩
    have hcover := hF.cover_preserve (G.is_cover_of_isCoverDense J Y)
    have hle : (Sieve.coverByImage G Y).functorPushforward F ≤
        (Sieve.coverByImage (G ⋙ F) X).pullback b := by
      rintro Z t ⟨Y', i, r, ⟨⟨d, p, q, hpq⟩⟩, ht⟩
      refine ⟨⟨d, r ≫ F.map p, F.map q ≫ b, ?_⟩⟩
      calc
        (r ≫ F.map p) ≫ (F.map q ≫ b) = (r ≫ F.map (p ≫ q)) ≫ b := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
        _ = (r ≫ F.map i) ≫ b := by rw [hpq]
        _ = t ≫ b := by rw [ht]
    have hb := K.superset_covering hle hcover
    rw [← fac, Sieve.pullback_comp]
    exact K.pullback_stable a hb

/-- Replacing the source of a cover-dense functor by an equivalent category preserves density. -/
theorem coverDense_precomp_equivalence (e : A ≌ B) (F : B ⥤ C)
    (K : GrothendieckTopology C) [F.IsCoverDense K] :
    (e.functor ⋙ F).IsCoverDense K where
  is_cover X := by
    apply K.superset_covering _ (F.is_cover_of_isCoverDense K X)
    rintro Y f ⟨⟨Z, a, b, hab⟩⟩
    let iso := F.mapIso (e.counitIso.app Z)
    refine ⟨⟨e.inverse.obj Z, a ≫ iso.inv, iso.hom ≫ b, ?_⟩⟩
    calc
      (a ≫ iso.inv) ≫ (iso.hom ≫ b) = a ≫ (iso.inv ≫ iso.hom ≫ b) := Category.assoc _ _ _
      _ = a ≫ b := congrArg (fun k ↦ a ≫ k) (iso.inv_hom_id_assoc b)
      _ = f := hab

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## PointedBasis -/

@[expose] public noncomputable section
open CategoryTheory
universe u v
namespace AlgebraicGeometry.GroupoidsOver.Sheafification
variable {D : Type u} [Category.{u} D] {C : Type v} [Category.{u} C]
  (F : D ⥤ C) (x : C)

/-- Add one specified object to a small chart family, retaining actual ambient morphisms. -/
def pointedObjects : Option D → C
  | none => x
  | some d => F.obj d

abbrev PointedBasis := InducedCategory C (pointedObjects F x)

def pointedInclusion : PointedBasis F x ⥤ C := inducedFunctor (pointedObjects F x)

instance : (pointedInclusion F x).Full := (fullyFaithfulInducedFunctor _).full
instance : (pointedInclusion F x).Faithful := (fullyFaithfulInducedFunctor _).faithful

/-- Adding an object and all morphisms preserves the original chart family's cover density. -/
theorem pointedCoverDense (J : GrothendieckTopology C) [F.IsCoverDense J] :
    (pointedInclusion F x).IsCoverDense J where
  is_cover Y := by
    apply J.superset_covering _ (F.is_cover_of_isCoverDense J Y)
    rintro W f ⟨⟨d, a, b, hab⟩⟩
    exact ⟨⟨(some d : PointedBasis F x), a, b, hab⟩⟩

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## FiberSliceCertificate -/

@[expose] public noncomputable section
open CategoryTheory
universe u v

namespace AlgebraicGeometry.GroupoidsOver.Sheafification
variable {C : Type u} {E : Type v} [Category C] [Category E]
  (p : E ⥤ C) [Functor.IsFibered.InGroupoids p] (x : E)

/-- The slice projection's inverse on morphisms is the actual Cartesian lift
factorization provided by the given groupoid fibration. -/
def fiberSliceFullyFaithful : (Over.post p : Over x ⥤ Over (p.obj x)).FullyFaithful where
  preimage {A B} f := by
    have hf : p.map A.hom = f.left ≫ p.map B.hom := (Over.w f).symm
    exact Over.homMk
      (Functor.IsStronglyCartesian.map p (p.map B.hom) B.hom hf A.hom)
      (Functor.IsStronglyCartesian.fac p (p.map B.hom) B.hom hf A.hom)
  map_preimage {A B} f := by
    ext
    have hf : p.map A.hom = f.left ≫ p.map B.hom := (Over.w f).symm
    exact (IsHomLift.eq_of_isHomLift p f.left
      (Functor.IsStronglyCartesian.map p (p.map B.hom) B.hom
        hf A.hom)).symm
  preimage_map {A B} f := by
    ext
    have hf : p.map A.hom = p.map f.left ≫ p.map B.hom := (Over.w ((Over.post p).map f)).symm
    exact (Functor.IsStronglyCartesian.map_uniq p (p.map B.hom) B.hom
      hf A.hom f.left (Over.w f)).symm

/-- Every base slice arrow is represented by the Cartesian pullback already
supplied by fibredness, rather than an admitted essential-surjectivity witness. -/
theorem fiberSliceEssSurj : (Over.post p : Over x ⥤ Over (p.obj x)).EssSurj where
  mem_essImage Y := by
    have hex : ∃ (b : E) (f : b ⟶ x), p.IsCartesian Y.hom f :=
      Functor.IsPreFibered.exists_isCartesian' Y.hom
    obtain ⟨b, f, hf⟩ := hex
    have hb : p.obj b = Y.left :=
      @IsHomLift.domain_eq _ _ _ _ p _ _ _ _ Y.hom f hf.toIsHomLift
    refine ⟨Over.mk f, ⟨Over.isoMk (eqToIso hb) ?_⟩⟩
    exact (show p.map f = eqToHom hb ≫ Y.hom from by
      simpa only [eqToHom_refl, Category.comp_id] using
        (@IsHomLift.fac' _ _ _ _ p _ _ _ _ Y.hom f hf.toIsHomLift)).symm

/-- The actual equivalence of slices follows from the two proved components. -/
theorem fiberSliceIsEquivalence :
    (Over.post p : Over x ⥤ Over (p.obj x)).IsEquivalence := by
  -- Local instance justification (instance diamond): use the proved Cartesian slice preimages for fullness, not a selected legacy equivalence.
  letI := (fiberSliceFullyFaithful p x).full
  -- Local instance justification (instance diamond): use the proved Cartesian slice preimages for faithfulness, not a selected legacy equivalence.
  letI := (fiberSliceFullyFaithful p x).faithful
  -- Local instance justification (instance diamond): the slice preimage used below comes from the given fibredness field and the proved essential-surjectivity certificate.
  letI := fiberSliceEssSurj p x
  exact { }

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## InheritedCertificate -/

@[expose] public noncomputable section
open CategoryTheory
universe u v w
namespace AlgebraicGeometry.GroupoidsOver.Sheafification
variable {C : Type u} {E : Type v} [Category.{w} C] [Category.{w} E]
  (p : E ⥤ C) [Functor.IsFibered.InGroupoids p] (J : GrothendieckTopology C)

/-- Every arrow in the given groupoid fibration is strongly Cartesian by
Mathlib's proved fibredness theorem, so the inherited precoverage is the comap. -/
theorem inheritedLift_eq : J.toPrecoverage.stronglyCartesianLift p = J.toPrecoverage.comap p := by
  ext x R
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro y f hf
    exact Functor.IsFibered.isStronglyCartesian_of_isCartesian p (p.map f) f

/-- The inherited topology agrees with the ordinary restricted topology;
this is proved from its actual precoverage definition. -/
theorem inherited_eq_restricted : p.inheritedTopology J = p.restrictedTopology J := by
  change (J.toPrecoverage.stronglyCartesianLift p).toGrothendieck =
    (J.toPrecoverage.comap p).toGrothendieck
  rw [inheritedLift_eq]

/-- Slice full faithfulness makes sieve pushforward followed by pullback exact,
even though the projection need not be fully faithful on the whole category. -/
theorem sieve_pull_push {x : E} (R : Sieve x) :
    (R.functorPushforward p).functorPullback p = R := by
  apply le_antisymm
  · rintro y f ⟨z, g, h, hg, hcomp⟩
    let a : Over.mk f ⟶ Over.mk g :=
      (fiberSliceFullyFaithful p x).preimage (Over.homMk h hcomp.symm)
    have ha : a.left ≫ g = f := Over.w a
    rw [← ha]
    exact R.downward_closed hg a.left
  · exact Sieve.le_functorPushforward_pullback _ _

/-- Slice essential surjectivity supplies every base arrow, and hence every
base sieve, by an actual Cartesian lift. -/
theorem sieve_push_pull {x : E} (R : Sieve (p.obj x)) :
    (R.functorPullback p).functorPushforward p = R := by
  apply le_antisymm
  · rintro y f ⟨z, g, h, hg, rfl⟩
    exact R.downward_closed hg h
  · intro y f hf
    -- Local instance justification (instance diamond): the slice preimage used below comes from the given fibredness field and the proved essential-surjectivity certificate.
    letI := fiberSliceEssSurj p x
    let F : Over x ⥤ Over (p.obj x) := Over.post p
    let A := F.objPreimage (Over.mk f)
    let e := F.objObjPreimageIso (Over.mk f)
    refine ⟨A.left, A.hom, e.inv.left, ?_, ?_⟩
    · change R (p.map A.hom)
      have he : e.hom.left ≫ f = p.map A.hom := Over.w e.hom
      rw [← he]
      exact R.downward_closed hf e.hom.left
    · exact (Over.w e.inv).symm

theorem sieve_push_pullback {x y : E} (f : y ⟶ x) (R : Sieve x) :
    (R.pullback f).functorPushforward p = (R.functorPushforward p).pullback (p.map f) := by
  have hinj : Function.Injective (Sieve.functorPullback p : Sieve (p.obj y) → Sieve y) := by
    intro A B h
    simpa only [sieve_push_pull] using congrArg (Sieve.functorPushforward p) h
  apply hinj
  simp only [sieve_pull_push, Sieve.functorPullback_pullback]

/-- The inherited topology written directly on sieves using the proved
equivalence of slice categories. -/
def directInherited : GrothendieckTopology E where
  sieves x := {R | R.functorPushforward p ∈ J (p.obj x)}
  top_mem' x := by
    apply J.superset_covering _ (J.top_mem (p.obj x))
    intro y f hf
    exact ⟨x, 𝟙 x, f, trivial, by simp⟩
  pullback_stable' {x y} R f hR := by
    change (R.pullback f).functorPushforward p ∈ J (p.obj y)
    rw [sieve_push_pullback]
    exact J.pullback_stable (p.map f) hR
  transitive' {x} R hR T hT := by
    change T.functorPushforward p ∈ J (p.obj x)
    apply J.transitive hR
    rintro y f ⟨z, g, h, hg, rfl⟩
    rw [Sieve.pullback_comp, ← sieve_push_pullback]
    exact J.pullback_stable h (hT hg)

/-- Every inherited covering sieve is exactly one whose image covers. -/
theorem directInherited_eq : directInherited p J = p.inheritedTopology J := by
  rw [inherited_eq_restricted]
  apply le_antisymm
  · intro x R hR
    exact Functor.mem_restrictedTopology_of_functorPushforward_mem hR
  · change (J.toPrecoverage.comap p).toGrothendieck ≤ directInherited p J
    rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro x R hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    change (Sieve.generate R).functorPushforward p ∈ J (p.obj x)
    rw [← Sieve.generate_map_eq_functorPushforward]
    exact hR

/-- The actual slice projection identifies the original inherited slice
topology with the corresponding base slice topology. -/
theorem fiberSliceDense (x : E) : (Over.post p : Over x ⥤ Over (p.obj x)).IsDenseSubsite
    ((p.inheritedTopology J).over x) (J.over (p.obj x)) := by
  -- Local instance justification (instance diamond): select the proved slice equivalence instead of the imported admitted overPost instance.
  letI := fiberSliceIsEquivalence p x
  refine { functorPushforward_mem_iff := ?_ }
  ·
    intro y R
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post, ← directInherited_eq]
    rfl

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## LocalSizeBridge -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace AlgebraicGeometry.GroupoidsOver.Sheafification

variable {D : Type u} [Category.{u} D] {C : Type (u + 1)} [Category.{u} C]
  (G : D ⥤ C) (J : GrothendieckTopology D) (K : GrothendieckTopology C)
  [G.IsContinuous J K] [G.IsCocontinuous J K]

include J in
/-- Restriction to a genuine small local site certifies the size of a section
of the upper-universe sheafification, at any object in that site's image. -/
theorem sectionSmall (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (d : D) :
    Small.{u} ((sheafify K (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).obj
      (op (G.obj d))) := by
  -- Local instance justification (defeq pin): explicitly restrict the forgetful functor from universe u+1 to u-sized filtered diagrams used by this local site.
  letI : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  -- Local instance justification (defeq pin): this is the larger-coefficient sheafification on the specific u-small local topology J used by the comparison.
  letI : HasSheafify J AddCommGrpCat.{u + 1} := inferInstance
  -- Local instance justification (defeq pin): specialize filtered-colimit preservation to the covering-sieve category of this local object V.
  letI (V : D) : PreservesColimitsOfShape (J.Cover V)ᵒᵖ (forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  -- Local instance justification (defeq pin): the comparison uses the universe lift on the local cover-indexed colimit, not colimits at arbitrary sizes.
  letI (V : D) : PreservesColimitsOfShape (J.Cover V)ᵒᵖ
      AddCommGrpCat.uliftFunctor.{u + 1, u} := inferInstance
  -- Local instance justification (defeq pin): fix the universe lift on this covering sieve multiequalizer before assembling the sheafification comparison.
  letI (V : D) (W : J.Cover V) (P : Dᵒᵖ ⥤ AddCommGrpCat.{u}) :
      PreservesLimit (W.index P).multicospan AddCommGrpCat.uliftFunctor.{u + 1, u} := inferInstance
  -- Local instance justification (defeq pin): the forgetful functor needs u-sized limits here while its native coefficient universe is u+1.
  letI : PreservesLimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) := inferInstance
  -- Local instance justification (search instability): select the concrete plus-construction comparison directly, avoiding recursive essentially-small-site instance search.
  letI : J.PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} :=
    GrothendieckTopology.instPreservesSheafification J AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e₁ := ((G.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u + 1} J K).app (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}))
  let e₂ := sheafifyComposeIso J AddCommGrpCat.uliftFunctor.{u + 1, u} (G.op ⋙ P)
  let e := ((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapIso e₁).symm ≪≫ e₂
  -- Local instance justification (defeq pin): expose that the compared section is literally a universe lift of a small abelian group.
  letI : Small.{u} ((sheafify J (G.op ⋙ P) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (op d)) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} ((sheafify J (G.op ⋙ P)).obj (op d))))
  exact small_of_injective (ConcreteCategory.bijective_of_isIso (e.hom.app (op d))).1

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## ShrinkSheaf -/

@[expose] public noncomputable section
open CategoryTheory Opposite
universe u v w

namespace AlgebraicGeometry.GroupoidsOver.Sheafification
variable {C : Type v} [Category.{w} C]

/-- Shrink only a presheaf whose section sizes have been proved; restrictions
are conjugated through the actual additive equivalences. -/
def shrinkAdd (F : C ⥤ AddCommGrpCat.{u + 1}) [∀ V, Small.{u} (F.obj V)] :
    C ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (Shrink.{u} (F.obj V))
  map f := AddCommGrpCat.ofHom
    (Shrink.addEquiv.symm.toAddMonoidHom.comp ((F.map f).hom.comp Shrink.addEquiv.toAddMonoidHom))
  map_id V := by ext x; simp
  map_comp f g := by ext x; simp

/-- The small carrier recovers the original group, with both directions
explicitly supplied by the proved-small equivalence. -/
def shrinkAddIso (F : C ⥤ AddCommGrpCat.{u + 1}) [∀ V, Small.{u} (F.obj V)] :
    shrinkAdd F ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅ F :=
  NatIso.ofComponents (fun V =>
    (show ULift.{u + 1} (Shrink.{u} (F.obj V)) ≃+ F.obj V from
      AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso) (by
        intro V W f
        ext x
        change Shrink.addEquiv (Shrink.addEquiv.symm
            ((F.map f) (Shrink.addEquiv x.down))) = (F.map f) (Shrink.addEquiv x.down)
        exact AddEquiv.apply_symm_apply _ _)

/-- Sheafness is reflected by the fully faithful universe lift, so shrinking
a proved-small sheaf preserves its actual sheaf condition. -/
theorem shrinkAdd_isSheaf (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) [∀ V, Small.{u} (F.obj V)]
    (hF : Presheaf.IsSheaf J F) : Presheaf.IsSheaf J (shrinkAdd F) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{u + 1, u}
  exact (Presheaf.isSheaf_of_iso_iff (shrinkAddIso F)).mpr hF

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## LowerSheafification -/

@[expose] public noncomputable section
open CategoryTheory Opposite
universe u v w

namespace AlgebraicGeometry.GroupoidsOver.Sheafification
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  (hs : ∀ (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (V : Cᵒᵖ),
    Small.{u} ((sheafify J (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).obj V))

/-- The unlifted sheafification object is the certified-small upper object;
its carrier, operations and restrictions are transported by explicit equivalences. -/
def lowerSheafificationObj (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Sheaf J AddCommGrpCat.{u} := by
  -- Local instance justification (proof-local temporary data): shrink this specific presheaf only with the section-size certificates supplied by the proved bound hs.
  letI := hs P
  exact ⟨shrinkAdd (sheafify J (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})),
    shrinkAdd_isSheaf J _ ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).property⟩

/-- Lifting the explicit small object recovers the given upper-universe sheafification. -/
def lowerLiftIso (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (lowerSheafificationObj J hs P) ≅
      (presheafToSheaf J AddCommGrpCat.{u + 1}).obj (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  -- Local instance justification (proof-local temporary data): shrink this specific presheaf only with the section-size certificates supplied by the proved bound hs.
  letI := hs P
  exact (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{u + 1}).preimageIso (shrinkAddIso _)

/-- The actual adjunction hom equivalence is transported along the two fully
faithful universe lifts and the proved-small object comparison. -/
def lowerHomEquiv (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (Q : Sheaf J AddCommGrpCat.{u}) :
    (lowerSheafificationObj J hs P ⟶ Q) ≃ (P ⟶ Q.obj) :=
  ((fullyFaithfulSheafCompose J (Functor.FullyFaithful.ofFullyFaithful
      AddCommGrpCat.uliftFunctor.{u + 1, u})).homEquiv.trans
    ((lowerLiftIso J hs P).homCongr (Iso.refl _))).trans
    (((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _).trans
      ((Functor.FullyFaithful.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u}).whiskeringRight Cᵒᵖ).homEquiv.symm)

set_option backward.isDefEq.respectTransparency false in
theorem lowerHomEquiv_comp (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (Q Q' : Sheaf J AddCommGrpCat.{u}) (g : Q ⟶ Q') (f : lowerSheafificationObj J hs P ⟶ Q) :
    lowerHomEquiv J hs P Q' (f ≫ g) = lowerHomEquiv J hs P Q f ≫ g.hom := by
  apply ((Functor.FullyFaithful.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u}).whiskeringRight Cᵒᵖ).map_injective
  change
    ((Functor.FullyFaithful.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u}).whiskeringRight Cᵒᵖ).homEquiv
      (((Functor.FullyFaithful.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u}).whiskeringRight Cᵒᵖ).homEquiv.symm _) =
      ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (lowerHomEquiv J hs P Q f ≫ g.hom)
  rw [Equiv.apply_symm_apply, Functor.map_comp]
  change _ =
    ((Functor.FullyFaithful.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u}).whiskeringRight Cᵒᵖ).homEquiv
      (((Functor.FullyFaithful.ofFullyFaithful AddCommGrpCat.uliftFunctor.{u + 1, u}).whiskeringRight Cᵒᵖ).homEquiv.symm _) ≫ _
  rw [Equiv.apply_symm_apply]
  change
    (sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _
      ((lowerLiftIso J hs P).inv ≫
        (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).map (f ≫ g) ≫ 𝟙 _) =
    (sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _
      ((lowerLiftIso J hs P).inv ≫
        (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).map f ≫ 𝟙 _) ≫ _
  simp only [Category.comp_id, Functor.map_comp, ← Category.assoc]
  exact (sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv_naturality_right _ _

include hs in
/-- A proved pointwise size bound lowers the sheafification adjunction itself;
the certificate is constructed from the explicit objects and hom equivalences. -/
theorem lowerHasWeakSheafify : HasWeakSheafify J AddCommGrpCat.{u} :=
  (Adjunction.adjunctionOfEquivLeft (lowerHomEquiv J hs) (lowerHomEquiv_comp J hs)).isRightAdjoint

end AlgebraicGeometry.GroupoidsOver.Sheafification

end
