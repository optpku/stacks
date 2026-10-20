module

public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.Stack.Coverwise
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.PrecompLift
public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Sites.Sheafification.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackification

A cartesian morphism of fibred categories is a stackification when its target is a stack and the
morphism is a local equivalence: its Hom-presheaf maps are local equivalences and every target
object is locally in its essential image.  This is the formal content of the two conditions in
Stacks Project, Lemma 8.8.1, and it implies the universal property against every stack.

## Main declarations

* `CategoryTheory.CartesianBasedFunctor.IsStackification` — the universe-polymorphic
  stackification predicate.
* `CategoryTheory.CartesianBasedFunctor.IsStackification.homSheafification` — the canonical
  Hom-presheaf sheafification presentation.
* `CategoryTheory.CartesianBasedFunctor.IsStackification.lift` — universal factorization.
* `CategoryTheory.CartesianBasedFunctor.IsStackification.precomp_isEquivalence` — the
  Hom-category universal property.
* `CategoryTheory.FiberedCategoryOver.Hom.IsStackification` — the fixed-universe specialization.
-/

@[expose] public section

-- The selected lifts expose private descent constructions through their explicit data fields.
set_option backward.privateInPublic true

universe u v w vS uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open Functor Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

/-- A cartesian based functor is a stackification when it is a local equivalence and its target is
a stack.  Thus its Hom-presheaf maps exhibit sheafification after passage to the localizing class,
and its target objects are locally in the essential image. Source and target total categories may
live in independent universes. -/
@[stacks 02ZM "stackification of a fibred category",
  stacks 02ZN "stackification predicate"]
class IsStackification
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop where
  /-- The comparison is a local equivalence of fibred categories. -/
  isLocalEquivalence : IsLocalEquivalence J F
  /-- The target projection is a stack over the site. -/
  isStack : IsStack.OnSite J p₂

attribute [instance] IsStackification.isStack
attribute [stacks 02ZN "stackification local-equivalence field"]
  IsStackification.isLocalEquivalence
attribute [stacks 02ZN "stackification target-stack field"]
  IsStackification.isStack

/-- The identity cartesian functor on a stack is a stackification. -/
instance IsStackification.id (J : GrothendieckTopology C) [IsStack.OnSite J p₁] :
    IsStackification J (CartesianBasedFunctor.id p₁) where
  isLocalEquivalence := IsLocalEquivalence.id J
  isStack := inferInstance

/-- The local-equivalence and target-stack conditions are exactly the defining conditions of a
universe-polymorphic stackification. -/
@[stacks 02ZN "defining conditions of a fibred-category stackification"]
theorem IsStackification.iff_isLocalEquivalence_and_isStack
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    IsStackification J F ↔
      IsLocalEquivalence J F ∧ IsStack.OnSite J p₂ := sorry

/-- On every fiber, the canonical Hom-presheaf map of a
stackification presents its target as the sheafification of its source. The target sheaf
condition and membership in the localizing class are exposed separately by
`Presheaf.IsSheafification.isSheaf` and `Presheaf.IsSheafification.mem_W`. -/
@[stacks 02ZP "Hom-presheaf sheafification condition",
  stacks 02ZN "stackification Hom-presheaf sheafification condition"]
theorem IsStackification.homSheafification
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsStackification J F) {U : C} (x y : p₁.Fiber U) :
    Presheaf.IsSheafification (J.over U)
      (HomPresheaf.Chosen.map F x y) := sorry

/-- Two heterogeneous lifts through a stackification are related by a unique isomorphism
compatible with their comparison isomorphisms. -/
@[stacks 0435 "uniqueness of heterogeneous stackification lifts"]
theorem IsStackification.liftIsoUnique
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (G₁ G₂ : CartesianBasedFunctor p₂ p₃)
    (α₁ : (precomp p₃ i).obj G₁ ≅ F)
    (α₂ : (precomp p₃ i).obj G₂ ≅ F) :
    ∃! β : G₁ ≅ G₂, (precomp p₃ i).mapIso β ≪≫ α₂ = α₁ := sorry

attribute [stacks 0436 "unique comparison of heterogeneous groupoid-stackification lifts"]
  IsStackification.liftIsoUnique

namespace IsStackification

/-! The universal-property theorem above is intentionally proposition-valued.  The following
    owner packages a factorization and its comparison as reusable Type-valued data, while keeping
    the existential theorem and the noncanonical choice boundary explicit. -/

/-- A chosen factorization through a heterogeneous stackification.

The fields are the actual downstream data: a lift and its comparison after precomposition.  The
stackification proof is not stored again, so this is a thin data owner rather than a second
stackification predicate. -/
@[stacks 0435 "explicit heterogeneous stackification lift data"]
structure LiftChoice
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {i : CartesianBasedFunctor p₁ p₂}
    (F : CartesianBasedFunctor p₁ p₃) where
  /-- The cartesian functor factoring `F` through `i`. -/
  lift : CartesianBasedFunctor p₂ p₃
  /-- The comparison between the precomposed lift and `F`. -/
  comparison : (precomp p₃ i).obj lift ≅ F

attribute [stacks 0435 "heterogeneous stackification lift field"]
  LiftChoice.lift
attribute [stacks 0435 "heterogeneous stackification lift comparison field"]
  LiftChoice.comparison

/-- Package explicitly supplied lift and comparison data. -/
@[stacks 0435 "package heterogeneous stackification lift data"]
def LiftChoice.of
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {i : CartesianBasedFunctor p₁ p₂}
    {F : CartesianBasedFunctor p₁ p₃}
    (G : CartesianBasedFunctor p₂ p₃)
    (α : (precomp p₃ i).obj G ≅ F) : LiftChoice (i := i) F :=
  ⟨G, α⟩

/-- Convert the proposition-level existential lift theorem into a named data package.

This is the only helper that eliminates the existential; callers with an explicit lift should
prefer `LiftChoice.of`, which does not select any witness. -/
@[stacks 0435 "package an existential stackification lift"]
noncomputable def LiftChoice.ofExists
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {i : CartesianBasedFunctor p₁ p₂}
    {F : CartesianBasedFunctor p₁ p₃}
    (h : ∃ G : CartesianBasedFunctor p₂ p₃,
      Nonempty ((precomp p₃ i).obj G ≅ F)) : LiftChoice (i := i) F where
  lift := Classical.choose h
  comparison := Classical.choice (Classical.choose_spec h)

set_option maxHeartbeats 2000000 in
/-- Effective descent of the local essential-image models gives a cartesian lift and its
comparison over the original source. All Hom maps are glued from actual local preimages. -/
private noncomputable def descentLift
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) : LiftChoice (i := i) F := by
  classical
  let χ₁ := Cleavage.ofIsFibered p₁
  let χ₂ := Cleavage.ofIsFibered p₂
  let χ₃ := Cleavage.ofIsFibered p₃
  let homImage {V : C} (x y : p₁.Fiber V)
      (g : (i.fiberFunctor V).obj x ⟶ (i.fiberFunctor V).obj y) :
      (F.fiberFunctor V).obj x ⟶ (F.fiberFunctor V).obj y := by
    let η := HomPresheaf.Chosen.map i x y
    let target := (Functor.fiberPseudofunctor p₃).presheafHom
      ((F.fiberFunctor V).obj x) ((F.fiberFunctor V).obj y)
    let unitX := Cleavage.Reindex.idIsoApp χ₂ V ((i.fiberFunctor V).obj x)
    let unitY := Cleavage.Reindex.idIsoApp χ₂ V ((i.fiberFunctor V).obj y)
    let homSection : (((Functor.fiberPseudofunctor p₂).presheafHom
        ((i.fiberFunctor V).obj x) ((i.fiberFunctor V).obj y)) ⋙
          uliftFunctor.{max vS₁ vS₂, vS₂}).obj (op (Over.mk (𝟙 V))) :=
      ULift.up (unitX.inv ≫ g ≫ unitY.hom)
    let cover := Presheaf.imageSieve η (U := Over.mk (𝟙 V)) homSection
    let family : Presieve.FamilyOfElements target cover.arrows := fun W h hh ↦
      let preimage := Presheaf.localPreimage η (U := op (Over.mk (𝟙 V))) homSection h hh
      (Reindex.mapIso F χ₁ χ₃ W.hom x).hom ≫
        (F.fiberFunctor W.left).map preimage.down ≫
          (Reindex.mapIso F χ₁ χ₃ W.hom y).inv
    have covering : cover ∈ (J.over V) (Over.mk (𝟙 V)) :=
      (hi.isLocalEquivalence.1 x y).2.imageSieve_mem homSection
    have compatible : family.Compatible := by sorry
    let sheaf := (isSheaf_iff_isSheaf_of_type (J.over V) target).1
      (Pseudofunctor.IsPrestack.isSheaf (F := Functor.fiberPseudofunctor p₃) J _ _)
    exact (Cleavage.Reindex.idIsoApp χ₃ V ((F.fiberFunctor V).obj x)).hom ≫
      (sheaf cover covering).amalgamate family compatible ≫
        (Cleavage.Reindex.idIsoApp χ₃ V ((F.fiberFunctor V).obj y)).inv
  let isoImage {V : C} (x y : p₁.Fiber V)
      (e : (i.fiberFunctor V).obj x ≅ (i.fiberFunctor V).obj y) :
      (F.fiberFunctor V).obj x ≅ (F.fiberFunctor V).obj y :=
    { hom := homImage x y e.hom
      inv := homImage y x e.inv
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  let cover {V : C} (y : p₂.Fiber V) : J.Cover V :=
    ⟨EssentialImage.sieve i y, hi.isLocalEquivalence.2 y⟩
  let model {V : C} (y : p₂.Fiber V) (I : (cover y).Arrow) : p₁.Fiber I.Y :=
    Classical.choose I.hf
  let modelIso {V : C} (y : p₂.Fiber V) (I : (cover y).Arrow) :
      (i.fiberFunctor I.Y).obj (model y I) ≅ χ₂.reindexObj I.f y :=
    Classical.choice (Classical.choose_spec I.hf)
  let overlap {V W : C} (y : p₂.Fiber V) (q : W ⟶ V)
      (I K : (cover y).Arrow) (a : W ⟶ I.Y) (b : W ⟶ K.Y)
      (ha : a ≫ I.f = q) (hb : b ≫ K.f = q) :
      (i.fiberFunctor W).obj (χ₁.reindexObj a (model y I)) ≅
        (i.fiberFunctor W).obj (χ₁.reindexObj b (model y K)) :=
    (Reindex.mapIso i χ₁ χ₂ a (model y I)).symm ≪≫
      (χ₂.reindex a).mapIso (modelIso y I) ≪≫
      (Cleavage.Reindex.compIsoApp χ₂ I.f a y).symm ≪≫
      eqToIso (congrArg (fun h ↦ χ₂.reindexObj h y) (ha.trans hb.symm)) ≪≫
      Cleavage.Reindex.compIsoApp χ₂ K.f b y ≪≫
      ((χ₂.reindex b).mapIso (modelIso y K)).symm ≪≫
      Reindex.mapIso i χ₁ χ₂ b (model y K)
  let datum {V : C} (y : p₂.Fiber V) :
      (Functor.fiberPseudofunctor p₃).DescentData (fun I : (cover y).Arrow ↦ I.f) :=
    { obj I := (F.fiberFunctor I.Y).obj (model y I)
      hom W q I K a b ha hb :=
        (Reindex.mapIso F χ₁ χ₃ a (model y I)).hom ≫
          homImage _ _ (overlap y q I K a b ha hb).hom ≫
            (Reindex.mapIso F χ₁ χ₃ b (model y K)).inv
      pullHom_hom := by sorry
      hom_self := by sorry
      hom_comp := by sorry }
  let effective {V : C} (y : p₂.Fiber V) :=
    @Functor.asEquivalence _ _ _ _
      ((Functor.fiberPseudofunctor p₃).toDescentData (fun I : (cover y).Arrow ↦ I.f))
      (Pseudofunctor.isEquivalence_toDescentData (Functor.fiberPseudofunctor p₃) _
        (by simpa only [GrothendieckTopology.Cover.ofArrows_eq] using (cover y).property))
  let glue {V : C} (y : p₂.Fiber V) : p₃.Fiber V :=
    (effective y).inverse.obj (datum y)
  let glueIso {V : C} (y : p₂.Fiber V) (I : (cover y).Arrow) :
      χ₃.reindexObj I.f (glue y) ≅ (F.fiberFunctor I.Y).obj (model y I) :=
    { hom := ((effective y).counitIso.app (datum y)).hom.hom I
      inv := ((effective y).counitIso.app (datum y)).inv.hom I
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  let mapFiber {V W : C} (y : p₂.Fiber V) (z : p₂.Fiber W) (g : V ⟶ W)
      (β : y ⟶ χ₂.reindexObj g z) : glue y ⟶ χ₃.reindexObj g (glue z) := by
    let R := EssentialImage.sieve i y ⊓ (EssentialImage.sieve i z).pullback g
    have hR : R ∈ J V := J.intersection_covering
      (hi.isLocalEquivalence.2 y) (J.pullback_stable g (hi.isLocalEquivalence.2 z))
    let sieve := (Sieve.overEquiv (Over.mk (𝟙 V))).symm R
    let target := (Functor.fiberPseudofunctor p₃).presheafHom (glue y)
      (χ₃.reindexObj g (glue z))
    let family : Presieve.FamilyOfElements target sieve.arrows := fun A h hh ↦
      let Iy : (cover y).Arrow := ⟨A.left, h.left, hh.1⟩
      let Iz : (cover z).Arrow := ⟨A.left, h.left ≫ g, hh.2⟩
      let localArrow := (modelIso y Iy).hom ≫ (χ₂.reindex h.left).map β ≫
        (Cleavage.Reindex.compIsoApp χ₂ g h.left z).inv ≫ (modelIso z Iz).inv
      let value := (glueIso y Iy).hom ≫ homImage _ _ localArrow ≫
        (glueIso z Iz).inv ≫ (Cleavage.Reindex.compIsoApp χ₃ g h.left (glue z)).hom
      -- A slice arrow into the identity has the displayed structural map.
      eqToHom (congrArg (fun t ↦ χ₃.reindexObj t (glue y))
        ((Over.w h).symm.trans (Category.comp_id _))) ≫
        value ≫ eqToHom (congrArg (fun t ↦ χ₃.reindexObj t (χ₃.reindexObj g (glue z)))
          ((Category.comp_id _).symm.trans (Over.w h)))
    have compatible : family.Compatible := by sorry
    let sheaf := (isSheaf_iff_isSheaf_of_type (J.over V) target).1
      (Pseudofunctor.IsPrestack.isSheaf (F := Functor.fiberPseudofunctor p₃) J _ _)
    exact (Cleavage.Reindex.idIsoApp χ₃ V (glue y)).hom ≫
      (sheaf sieve (J.overEquiv_symm_mem_over _ _ hR)).amalgamate family compatible ≫
        (Cleavage.Reindex.idIsoApp χ₃ V (χ₃.reindexObj g (glue z))).inv
  let G : CartesianBasedFunctor p₂ p₃ := ofBasedFunctor
    { toFunctor :=
        { obj y := (glue (⟨y, rfl⟩ : p₂.Fiber (p₂.obj y))).1
          map {y z} φ :=
            (mapFiber ⟨y, rfl⟩ ⟨z, rfl⟩ (p₂.map φ) (χ₂.verticalFactor φ)).1 ≫
              χ₃.cartesianHom (p₂.map φ) (glue ⟨z, rfl⟩)
          map_id := by sorry
          map_comp := by sorry }
      w := by sorry }
    (by sorry)
  let comparison {V : C} (x : p₁.Fiber V) :
      glue ((i.fiberFunctor V).obj x) ≅ (F.fiberFunctor V).obj x := by
    let y := (i.fiberFunctor V).obj x
    let localIso (I : (cover y).Arrow) :
        (F.fiberFunctor I.Y).obj (model y I) ≅
          χ₃.reindexObj I.f ((F.fiberFunctor V).obj x) :=
      isoImage _ _ (modelIso y I ≪≫ Reindex.mapIso i χ₁ χ₂ I.f x) ≪≫
        (Reindex.mapIso F χ₁ χ₃ I.f x).symm
    let d : datum y ≅ ((effective y).functor.obj ((F.fiberFunctor V).obj x)) :=
      Pseudofunctor.DescentData.isoMk localIso (by sorry)
    exact (effective y).inverse.mapIso d ≪≫
      ((effective y).unitIso.app ((F.fiberFunctor V).obj x)).symm
  let e : i.toBasedFunctor.comp G.toBasedFunctor ≅ F.toBasedFunctor := by
    -- Composition in the based-functor category is written in source-to-target order below.
    exact BasedNatIso.ofComponents (fun x ↦
      Functor.Fiber.fiberInclusion.mapIso
        (comparison (⟨x, by sorry⟩ : p₁.Fiber (p₂.obj (i.toFunctor.obj x)))))
      (by sorry) (by sorry)
  exact ⟨G, ObjectProperty.isoMk _ e⟩

/-- The comparison of the effective-descent lift with the original cartesian functor. -/
private noncomputable def descentLiftComparison
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    (precomp p₃ i).obj (descentLift hi F).lift ≅ F :=
  (descentLift hi F).comparison

/-- Comparisons between two lifts are obtained by gluing their actual local components on
an essential-image cover of each target object. -/
private noncomputable def descentComparison
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) : L₁.lift ≅ L₂.lift := by
  classical
  let χ₁ := Cleavage.ofIsFibered p₁
  let χ₂ := Cleavage.ofIsFibered p₂
  let χ₃ := Cleavage.ofIsFibered p₃
  let cover {V : C} (y : p₂.Fiber V) : J.Cover V :=
    ⟨EssentialImage.sieve i y, hi.isLocalEquivalence.2 y⟩
  let localIso {V : C} (y : p₂.Fiber V) (I : (cover y).Arrow) :
      χ₃.reindexObj I.f ((L₁.lift.fiberFunctor V).obj y) ≅
        χ₃.reindexObj I.f ((L₂.lift.fiberFunctor V).obj y) :=
    let x := Classical.choose I.hf
    let e := Classical.choice (Classical.choose_spec I.hf)
    Reindex.mapIso L₁.lift χ₂ χ₃ I.f y ≪≫
      (L₁.lift.fiberFunctor I.Y).mapIso e.symm ≪≫
      (BasedNatIso.fiber (toBasedIso L₁.comparison) I.Y).app x ≪≫
      ((BasedNatIso.fiber (toBasedIso L₂.comparison) I.Y).app x).symm ≪≫
      (L₂.lift.fiberFunctor I.Y).mapIso e ≪≫
      (Reindex.mapIso L₂.lift χ₂ χ₃ I.f y).symm
  let component {V : C} (y : p₂.Fiber V) :
      (L₁.lift.fiberFunctor V).obj y ≅ (L₂.lift.fiberFunctor V).obj y := by
    let sieve := (Sieve.overEquiv (Over.mk (𝟙 V))).symm (cover y).val
    let target := (Functor.fiberPseudofunctor p₃).presheafHom
      ((L₁.lift.fiberFunctor V).obj y) ((L₂.lift.fiberFunctor V).obj y)
    let reverse := (Functor.fiberPseudofunctor p₃).presheafHom
      ((L₂.lift.fiberFunctor V).obj y) ((L₁.lift.fiberFunctor V).obj y)
    let family : Presieve.FamilyOfElements target sieve.arrows := fun A h hh ↦
      let I : (cover y).Arrow := ⟨A.left, h.left, hh⟩
      eqToHom (congrArg (fun t ↦ χ₃.reindexObj t ((L₁.lift.fiberFunctor V).obj y))
        ((Over.w h).symm.trans (Category.comp_id _))) ≫
        (localIso y I).hom ≫
          eqToHom (congrArg (fun t ↦ χ₃.reindexObj t ((L₂.lift.fiberFunctor V).obj y))
          ((Category.comp_id _).symm.trans (Over.w h)))
    let inverseFamily : Presieve.FamilyOfElements reverse sieve.arrows := fun A h hh ↦
      let I : (cover y).Arrow := ⟨A.left, h.left, hh⟩
      eqToHom (congrArg (fun t ↦ χ₃.reindexObj t ((L₂.lift.fiberFunctor V).obj y))
        ((Over.w h).symm.trans (Category.comp_id _))) ≫
        (localIso y I).inv ≫
          eqToHom (congrArg (fun t ↦ χ₃.reindexObj t ((L₁.lift.fiberFunctor V).obj y))
          ((Category.comp_id _).symm.trans (Over.w h)))
    let sheaf := (isSheaf_iff_isSheaf_of_type (J.over V) target).1
      (Pseudofunctor.IsPrestack.isSheaf (F := Functor.fiberPseudofunctor p₃) J _ _)
    let reverseSheaf := (isSheaf_iff_isSheaf_of_type (J.over V) reverse).1
      (Pseudofunctor.IsPrestack.isSheaf (F := Functor.fiberPseudofunctor p₃) J _ _)
    let covering := J.overEquiv_symm_mem_over (Over.mk (𝟙 V)) _ (cover y).property
    exact
      { hom := (Cleavage.Reindex.idIsoApp χ₃ V _).hom ≫
          (sheaf sieve covering).amalgamate family (by sorry) ≫
            (Cleavage.Reindex.idIsoApp χ₃ V _).inv
        inv := (Cleavage.Reindex.idIsoApp χ₃ V _).hom ≫
          (reverseSheaf sieve covering).amalgamate inverseFamily (by sorry) ≫
            (Cleavage.Reindex.idIsoApp χ₃ V _).inv
        hom_inv_id := by sorry
        inv_hom_id := by sorry }
  exact ObjectProperty.isoMk _ (BasedNatIso.ofComponents
    (fun y ↦ Functor.Fiber.fiberInclusion.mapIso (component ⟨y, rfl⟩))
    (by sorry) (by sorry))

/-- The stackification universal property supplies a nonempty type of lift packages. -/
@[stacks 0435 "existence of heterogeneous stackification lift data"]
theorem LiftChoice.nonempty
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    Nonempty (LiftChoice (i := i) F) := ⟨descentLift hi F⟩

/-- A cartesian lift formed by effective descent of the local essential-image models. -/
@[irreducible, stacks 0435 "selected heterogeneous stackification lift"]
noncomputable def liftChoice
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) : LiftChoice (i := i) F :=
  descentLift hi F

/-- The comparison carried by the selected heterogeneous lift.

This is a named data readout, not a second existential theorem: the comparison remains the field
owner of `LiftChoice`, while this definition gives callers a stable name when they use the
noncanonical convenience value. -/
@[stacks 0435 "selected heterogeneous stackification lift comparison"]
noncomputable def liftChoiceComparison
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    (precomp p₃ i).obj (liftChoice hi F).lift ≅ F :=
  (liftChoice hi F).comparison

/-- Any two explicit lift choices have a unique compatible comparison. -/
@[stacks 0435 "existence and uniqueness of heterogeneous stackification lift comparisons"]
theorem LiftChoice.existsUniqueComparisonIso
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) :
    ∃! β : L₁.lift ≅ L₂.lift,
      (precomp p₃ i).mapIso β ≪≫ L₂.comparison = L₁.comparison := sorry

/-- The canonical comparison between two explicit lift choices. -/
@[stacks 0435 "comparison of heterogeneous stackification lift choices"]
noncomputable def LiftChoice.comparisonIso
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) : L₁.lift ≅ L₂.lift :=
  descentComparison hi L₁ L₂

/-- The comparison of two lift choices has the expected precomposition compatibility. -/
@[stacks 0435 "comparison specification for heterogeneous stackification lift choices"]
theorem LiftChoice.comparisonIso_spec
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) :
    (precomp p₃ i).mapIso (L₁.comparisonIso hi L₂) ≪≫ L₂.comparison = L₁.comparison := sorry

/-- Any compatible comparison between two lift choices equals the selected one. -/
@[stacks 0435 "uniqueness of selected heterogeneous stackification lift comparison"]
theorem LiftChoice.comparisonIso_unique
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F)
    (β : L₁.lift ≅ L₂.lift)
    (hβ : (precomp p₃ i).mapIso β ≪≫ L₂.comparison = L₁.comparison) :
    β = L₁.comparisonIso hi L₂ := sorry

end IsStackification

/-- Any cartesian morphism from the source of a stackification to another stack factors through
the stackification, without requiring the three total categories to share universes. -/
@[stacks 0435 "heterogeneous stackification lift"]
theorem IsStackification.lift
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    ∃ G : CartesianBasedFunctor p₂ p₃,
      Nonempty ((precomp p₃ i).obj G ≅ F) := ⟨(liftChoice hi F).lift, ⟨(liftChoice hi F).comparison⟩⟩

attribute [stacks 0436 "factorization through a groupoid stackification"]
  IsStackification.lift


/-- Heterogeneous precomposition by a stackification is an equivalence on cartesian
Hom-categories into every stack. -/
@[stacks 04W9 "heterogeneous universal property of stackification"]
theorem IsStackification.precomp_isEquivalence
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃] :
    (precomp p₃ i).IsEquivalence := sorry

attribute [stacks 0436 "heterogeneous Hom equivalence induced by groupoid stackification"]
  IsStackification.precomp_isEquivalence


end CartesianBasedFunctor

namespace FiberedCategoryOver.Hom

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- A morphism `i : X ⟶ Y` of fibred categories is a stackification of `X` when its cartesian
functor is a local equivalence and `Y` is a stack. This is the fixed-owner view of
`CartesianBasedFunctor.IsStackification`. -/
@[stacks 02ZM "fixed-universe stackification predicate"]
abbrev IsStackification (J : GrothendieckTopology C) (i : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsStackification J
    (FiberedCategoryOver.toCartesianBasedFunctor i)

/-- The fixed-owner stackification predicate is exactly local equivalence together with the target
stack condition. -/
@[stacks 02ZN "fixed-universe defining conditions of stackification"]
theorem IsStackification.iff_isLocalEquivalence_and_isStack
    (J : GrothendieckTopology C) (i : X ⟶ Y) :
    IsStackification J i ↔
      IsLocalEquivalence J i ∧ IsStack.OnSite J Y.p := sorry

/-- A fixed-universe stackification has a stack as its target projection.

This is the explicit readout counterpart of the instance carried by the heterogeneous owner.  It
is useful for downstream statements that want the target-stack hypothesis as an ordinary term
without relying on typeclass search or unfolding the fixed-universe abbreviation. -/
@[stacks 02ZN "fixed-universe target-stack readout"]
theorem IsStackification.isStack
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (h : IsStackification J i) :
    IsStack.OnSite J Y.p := sorry

/-- Two factorizations through a stackification are related by a unique `2`-isomorphism
compatible with their comparison isomorphisms.

It remembers the chosen factorization cells and characterizes the comparison between the lifts,
rather than merely asserting that the two lifts are isomorphic. -/
@[stacks 0435 "uniqueness of fixed-universe stackification lifts"]
theorem IsStackification.liftIsoUnique
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y} (h : IsStackification J i)
    [IsStack.OnSite J Z.p] {F : X ⟶ Z}
    (G₁ G₂ : Y ⟶ Z) (α₁ : i ≫ G₁ ≅ F) (α₂ : i ≫ G₂ ≅ F) :
    ∃! β : G₁ ≅ G₂,
      (Bicategory.precomp Z i).mapIso β ≪≫ α₂ = α₁ := sorry

namespace IsStackification

/-! The fixed-universe choice owner mirrors the heterogeneous `CartesianBasedFunctor` API.  It is
    a thin bundled readout: the defining predicate remains the abbreviation above, and all
    noncanonical data is confined to this explicit choice boundary. -/

/-- A chosen factorization through a fixed-universe stackification. -/
@[stacks 0435 "explicit fixed-universe stackification lift data"]
structure LiftChoice
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {i : X ⟶ Y} (F : X ⟶ Z) where
  /-- The bundled lift through the stackification target. -/
  lift : Y ⟶ Z
  /-- The comparison after precomposition with the stackification map. -/
  comparison : i ≫ lift ≅ F

attribute [stacks 0435 "fixed-universe stackification lift field"] LiftChoice.lift
attribute [stacks 0435 "fixed-universe stackification lift comparison field"] LiftChoice.comparison

/-- Package explicitly supplied fixed-universe lift data. -/
@[stacks 0435 "package fixed-universe stackification lift data"]
def LiftChoice.of
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {i : X ⟶ Y} {F : X ⟶ Z}
    (G : Y ⟶ Z) (α : i ≫ G ≅ F) : LiftChoice (i := i) F :=
  ⟨G, α⟩

/-- Convert the fixed-universe lift existence theorem into one named data package. -/
@[stacks 0435 "package an existential fixed-universe stackification lift"]
noncomputable def LiftChoice.ofExists
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {i : X ⟶ Y} {F : X ⟶ Z}
    (h : ∃ G : Y ⟶ Z, Nonempty (i ≫ G ≅ F)) : LiftChoice (i := i) F where
  lift := Classical.choose h
  comparison := Classical.choice (Classical.choose_spec h)

/-- A convenient selected fixed-universe lift. -/
@[stacks 0435 "selected fixed-universe stackification lift"]
noncomputable def liftChoice
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    (F : X ⟶ Z) : LiftChoice (i := i) F :=
  let L := CartesianBasedFunctor.IsStackification.liftChoice hi
    (FiberedCategoryOver.toCartesianBasedFunctor F)
  ⟨FiberedCategoryOver.ofBasedFunctor L.lift.toBasedFunctor L.lift.preservesStronglyCartesian,
    FiberedCategoryOver.BasedFunctorIso.lift (CartesianBasedFunctor.toBasedIso L.comparison)⟩

/-- A fixed-universe stackification supplies a nonempty type of lift packages. -/
@[stacks 0435 "existence of fixed-universe stackification lift data"]
theorem LiftChoice.nonempty
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    (F : X ⟶ Z) : Nonempty (LiftChoice (i := i) F) := ⟨liftChoice hi F⟩

/-- The comparison carried by the selected fixed-universe lift. -/
@[stacks 0435 "selected fixed-universe stackification lift comparison"]
noncomputable def liftChoiceComparison
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    (F : X ⟶ Z) : i ≫ (liftChoice hi F).lift ≅ F :=
  (liftChoice hi F).comparison

/-- Any two fixed-universe lift choices admit a unique compatible comparison. -/
@[stacks 0435 "existence and uniqueness of fixed-universe stackification lifts"]
theorem LiftChoice.existsUniqueComparisonIso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F) :
    ∃! β : L₁.lift ≅ L₂.lift,
      (Bicategory.precomp Z i).mapIso β ≪≫ L₂.comparison = L₁.comparison := sorry

/-- The selected comparison between two fixed-universe lift choices. -/
@[stacks 0435 "comparison of fixed-universe stackification lifts"]
noncomputable def LiftChoice.comparisonIso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F) : L₁.lift ≅ L₂.lift :=
  let toChoice (L : LiftChoice (i := i) F) :
      CartesianBasedFunctor.IsStackification.LiftChoice
        (i := FiberedCategoryOver.toCartesianBasedFunctor i)
        (FiberedCategoryOver.toCartesianBasedFunctor F) :=
    ⟨FiberedCategoryOver.toCartesianBasedFunctor L.lift,
      ObjectProperty.isoMk _ (FiberedCategoryOver.toBasedFunctorIso L.comparison)⟩
  FiberedCategoryOver.BasedFunctorIso.lift (CartesianBasedFunctor.toBasedIso
    (CartesianBasedFunctor.IsStackification.descentComparison hi (toChoice L₁) (toChoice L₂)))

/-- The selected fixed-universe lift comparison has the expected compatibility equation. -/
@[stacks 0435 "specification of fixed-universe stackification lift comparison"]
theorem LiftChoice.comparisonIso_spec
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F) :
    (Bicategory.precomp Z i).mapIso (LiftChoice.comparisonIso hi L₁ L₂) ≪≫
        L₂.comparison = L₁.comparison := sorry

/-- Any compatible fixed-universe lift comparison equals the selected one. -/
@[stacks 0435 "uniqueness of fixed-universe stackification lift comparison"]
theorem LiftChoice.comparisonIso_unique
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F)
    (β : L₁.lift ≅ L₂.lift)
    (hβ : (Bicategory.precomp Z i).mapIso β ≪≫ L₂.comparison = L₁.comparison) :
    β = LiftChoice.comparisonIso hi L₁ L₂ := sorry

end IsStackification

/-- The universal property of stackification: any morphism to a stack factors through the
stackification. The stackification witness is an explicit method argument so a caller holding a
one-off witness need not install a local instance. -/
@[stacks 0435]
theorem IsStackification.lift
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y} (h : IsStackification J i)
    [IsStack.OnSite J Z.p] (F : X ⟶ Z) :
    ∃ G : Y ⟶ Z, Nonempty (i ≫ G ≅ F) := ⟨(IsStackification.liftChoice h F).lift, ⟨(IsStackification.liftChoice h F).comparison⟩⟩


/-- The fixed-owner specialization of the universal Hom-category property of stackification. -/
@[stacks 04W9 "fixed-universe Hom property of stackification"]
theorem IsStackification.precomp_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y} (h : IsStackification J i)
    [IsStack.OnSite J Z.p] :
    (Bicategory.precomp Z i).IsEquivalence := sorry


end FiberedCategoryOver.Hom

end CategoryTheory
