/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Topos
public import ReasLib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Module pushforward along a closed immersion of ringed spaces

The main statements retain the minimal hypotheses: a closed embedding on underlying spaces and
local surjectivity of the structure-sheaf map.  Thin specializations to
`RingedSpace.IsClosedImmersion` are provided separately.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

/-- Pushforward of module sheaves is exact when the underlying map is a closed embedding. -/
@[stacks 08KS "(1)"]
theorem exact (hi : Topology.IsClosedEmbedding i.hom.base) :
    exactFunctor Z.Modules X.Modules (pushforward i) := sorry

/-- Precomposition on additive presheaves along the map on opens of an inducing map is
fully faithful. Its inverse on morphisms uses the explicit trace-hull isomorphism. -/
noncomputable def presheafPushforwardFullyFaithful
    (hi : Topology.IsInducing i.hom.base) :
    ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      (TopologicalSpace.Opens.map i.hom.base).op).FullyFaithful := by
  let e : hi.functor.op ⋙ (TopologicalSpace.Opens.map i.hom.base).op ≅ 𝟭 _ :=
    NatIso.ofComponents (fun U ↦
      eqToIso (congrArg op (hi.map_functorObj U.unop)))
  let unitIso (M : (TopologicalSpace.Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      M ≅ (hi.functor.op ⋙ (TopologicalSpace.Opens.map i.hom.base).op) ⋙ M :=
    (Functor.isoWhiskerRight e M).symm
  let adj := (hi.adjunction.op).whiskerLeft AddCommGrpCat.{u}
  have hunit (M : (TopologicalSpace.Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      (unitIso M).hom = adj.unit.app M := by
    apply NatTrans.ext
    funext U
    change M.map _ = M.map _
    congr 1
  letI : IsIso adj.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← hunit M]
    infer_instance
  refine
    { preimage := fun {M N} f ↦ adj.homEquiv M _ f ≫ (unitIso N).inv
      map_preimage := ?_
      preimage_map := ?_ }
  · intro M N f
    have heq : (unitIso N).inv = inv (adj.unit.app N) := by
      apply IsIso.eq_inv_of_hom_inv_id (f := adj.unit.app N)
      rw [← hunit N]
      exact (unitIso N).hom_inv_id
    rw [heq]
    exact adj.fullyFaithfulLOfIsIsoUnit.map_preimage f
  · intro M N f
    have heq : (unitIso N).inv = inv (adj.unit.app N) := by
      apply IsIso.eq_inv_of_hom_inv_id (f := adj.unit.app N)
      rw [← hunit N]
      exact (unitIso N).hom_inv_id
    rw [heq]
    exact adj.fullyFaithfulLOfIsIsoUnit.preimage_map f

/-- Recover the additive presheaf morphism on each open of the source by using its
largest ambient open extension. -/
noncomputable def pushforwardPreimageAdditive
    (hi : Topology.IsInducing i.hom.base) {F G : Z.Modules}
    (f : (pushforward i).obj F ⟶ (pushforward i).obj G) :
    F.val.presheaf ⟶ G.val.presheaf :=
  (presheafPushforwardFullyFaithful i hi).preimage ((PresheafOfModules.toPresheaf _).map f.val)

/-- The recovered additive morphism pushes forward to the given morphism. -/
theorem pushforwardPreimageAdditive_map
    (hi : Topology.IsInducing i.hom.base) {F G : Z.Modules}
    (f : (pushforward i).obj F ⟶ (pushforward i).obj G) :
    Functor.whiskerLeft (TopologicalSpace.Opens.map i.hom.base).op (pushforwardPreimageAdditive i hi f) =
    (PresheafOfModules.toPresheaf _).map f.val :=
  (presheafPushforwardFullyFaithful i hi).map_preimage _

/-- Local surjectivity of the structure map makes the recovered additive morphism linear. -/
theorem pushforwardPreimageAdditive_smul
    (hi : Topology.IsInducing i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    {F G : Z.Modules} (f : (pushforward i).obj F ⟶ (pushforward i).obj G)
    (U : (TopologicalSpace.Opens Z)ᵒᵖ) (r : Z.ringCatSheaf.obj.obj U) (m : F.val.obj U) :
    (pushforwardPreimageAdditive i hi f).app U (r • m) = r • (pushforwardPreimageAdditive i hi f).app U m := by
  letI : Sheaf.IsLocallySurjective (RingedSpace.Hom.toRingCatSheafHom i) :=
    ⟨fun s ↦ Presheaf.imageSieve_mem _
      (RingedSpace.Hom.commRingSheafPushforwardMap i).hom s⟩
  let M := (PresheafOfModules.pushforward
      (F := TopologicalSpace.Opens.map i.hom.base) (𝟙 _)).obj F.val
  let N := (PresheafOfModules.pushforward
      (F := TopologicalSpace.Opens.map i.hom.base) (𝟙 _)).obj G.val
  let f' : M ⟶ N :=
    (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (RingedSpace.Hom.toRingCatSheafHom i).hom
        ((pushforward i).obj G).isSheaf).symm f.val
  have linear (V : (TopologicalSpace.Opens X)ᵒᵖ) :
      ∀ (r : Z.ringCatSheaf.obj.obj ((TopologicalSpace.Opens.map i.hom.base).op.obj V))
        (m : F.val.obj ((TopologicalSpace.Opens.map i.hom.base).op.obj V)),
      (pushforwardPreimageAdditive i hi f).app ((TopologicalSpace.Opens.map i.hom.base).op.obj V) (r • m) =
        r • (pushforwardPreimageAdditive i hi f).app ((TopologicalSpace.Opens.map i.hom.base).op.obj V) m := by
    intro r m
    have h := congrArg (fun t => t.app V) (pushforwardPreimageAdditive_map i hi f)
    change (pushforwardPreimageAdditive i hi f).app ((TopologicalSpace.Opens.map i.hom.base).op.obj V) = _ at h
    rw [h]
    exact (f'.app V).hom.map_smul r m
  have hU : (TopologicalSpace.Opens.map i.hom.base).op.obj
      (op (hi.functor.obj U.unop)) = U :=
    congrArg op (hi.map_functorObj U.unop)
  have h := linear (op (hi.functor.obj U.unop))
  rw [hU] at h
  exact h r m

/-- The explicit inverse on Hom sets for module pushforward along a closed embedding with
locally surjective structure-sheaf map. -/
@[stacks 08KS "(2)"]
noncomputable def fullyFaithful
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    (pushforward i).FullyFaithful where
  preimage f :=
    ⟨PresheafOfModules.homMk (pushforwardPreimageAdditive i hi.isInducing f)
      (pushforwardPreimageAdditive_smul i hi.isInducing f)⟩
  map_preimage f := by
    ext U m
    exact congrArg (fun t => t.app U m) (pushforwardPreimageAdditive_map i hi.isInducing f)
  preimage_map f := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.toPresheaf _).map_injective
    change pushforwardPreimageAdditive i hi.isInducing ((pushforward i).map f) = (PresheafOfModules.toPresheaf _).map f.val
    exact (presheafPushforwardFullyFaithful i hi.isInducing).preimage_map ((PresheafOfModules.toPresheaf _).map f.val)

/-- The counit of pullback followed by pushforward is invertible for a closed embedding with
locally surjective structure-sheaf map. -/
theorem counitAppIsIso
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (F : Z.Modules) :
    IsIso ((RingedSpace.Hom.pullbackPushforwardAdjunction i).counit.app F) := by
  letI := (fullyFaithful i hi).full
  letI := (fullyFaithful i hi).faithful
  infer_instance

/-- The essential image of module pushforward consists exactly of modules annihilated by the
kernel of the structure-sheaf map. -/
@[stacks 08KS "(3)"]
theorem mem_essImage_iff
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (G : X.Modules) :
    (pushforward i).essImage G ↔
      SheafOfModules.IsAnnihilatedByKernel (RingedSpace.Hom.toRingCatSheafHom i) G := sorry

/-- A module lies in the essential image of pushforward exactly when every local section of the
defining ideal sheaf acts by zero. -/
@[stacks 08KS "(3), ideal-sheaf formulation in minimal generality"]
theorem mem_essImage_iff_idealSheaf_smul_eq_zero
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (G : X.Modules) :
    (pushforward i).essImage G ↔
      ∀ U : TopologicalSpace.Opens X,
        ∀ s : (RingedSpace.Hom.idealSheaf i).val.obj (op U),
          ∀ m : G.val.obj (op U),
            ((RingedSpace.Hom.idealSheafι i).val.app (op U) s) • m = 0 := sorry

/-- For the same minimal hypotheses, membership in the essential image is equivalent to
invertibility of the pullback-pushforward unit component. -/
theorem mem_essImage_iff_isIso_unit_app
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (G : X.Modules) :
    (pushforward i).essImage G ↔
      IsIso ((RingedSpace.Hom.pullbackPushforwardAdjunction i).unit.app G) := sorry

end AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion

namespace AlgebraicGeometry.RingedSpace.IsClosedImmersion

variable {X Z : RingedSpace.{u}} {i : Z ⟶ X}

/-- Pushforward of module sheaves along a closed immersion of ringed spaces is exact. -/
theorem pushforwardExact [RingedSpace.IsClosedImmersion i] :
    exactFunctor Z.Modules X.Modules (pushforward i) := sorry

/-- The canonical fully faithful datum for module pushforward along a closed immersion of
ringed spaces. -/
noncomputable def pushforwardFullyFaithful [RingedSpace.IsClosedImmersion i] :
    (pushforward i).FullyFaithful :=
  letI : Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
    RingedSpace.IsClosedImmersion.toIsLocallySurjective (i := i)
  RingedSpace.Hom.ModulePushforward.ClosedImmersion.fullyFaithful i
    (RingedSpace.IsClosedImmersion.isClosedEmbedding (i := i))

/-- Pushforward along a closed immersion induces an equivalence on every Hom set. -/
@[stacks 08KS "(2), Hom equivalence"]
noncomputable def pushforwardHomEquiv [RingedSpace.IsClosedImmersion i]
    (F G : Z.Modules) :
    (F ⟶ G) ≃ ((pushforward i).obj F ⟶ (pushforward i).obj G) :=
  (pushforwardFullyFaithful (i := i)).homEquiv

/-- The forward map of the pushforward Hom equivalence is functorial pushforward. -/
@[simp]
theorem pushforwardHomEquiv_apply [RingedSpace.IsClosedImmersion i]
    (F G : Z.Modules) (f : F ⟶ G) :
    pushforwardHomEquiv (i := i) F G f = (pushforward i).map f := rfl

/-- Module pushforward along a closed immersion is also a left adjoint, hence preserves all
small colimits. -/
@[stacks 01C3 "closed pushforward preserves colimits"]
instance pushforward_isLeftAdjoint [RingedSpace.IsClosedImmersion i] :
    (pushforward i).IsLeftAdjoint := sorry

/-- A module sheaf lies in the essential image of pushforward along a closed immersion exactly
when the kernel of the structure-sheaf map annihilates it. -/
theorem mem_essImage_iff [RingedSpace.IsClosedImmersion i] (G : X.Modules) :
    (pushforward i).essImage G ↔
      SheafOfModules.IsAnnihilatedByKernel (RingedSpace.Hom.toRingCatSheafHom i) G := sorry

/-- A module lies in the essential image of pushforward along a closed immersion exactly when
every local section of its defining ideal sheaf acts by zero. -/
@[stacks 08KS "(3), closed-immersion ideal-sheaf specialization"]
theorem mem_essImage_iff_idealSheaf_smul_eq_zero
    [RingedSpace.IsClosedImmersion i] (G : X.Modules) :
    (pushforward i).essImage G ↔
      ∀ U : TopologicalSpace.Opens X,
        ∀ s : (RingedSpace.Hom.idealSheaf i).val.obj (op U),
          ∀ m : G.val.obj (op U),
            ((RingedSpace.Hom.idealSheafι i).val.app (op U) s) • m = 0 := sorry

/-- A module sheaf lies in the essential image of pushforward along a closed immersion exactly
when its pullback-pushforward unit component is invertible. -/
theorem mem_essImage_iff_isIso_unit_app
    [RingedSpace.IsClosedImmersion i] (G : X.Modules) :
    (pushforward i).essImage G ↔
      IsIso ((RingedSpace.Hom.pullbackPushforwardAdjunction i).unit.app G) := sorry

/-- The full subcategory of `X.Modules` consisting of modules annihilated by the kernel of the
structure-sheaf map of `i`. -/
@[stacks 08KS "modules annihilated by the closed-immersion ideal"]
abbrev annihilated (i : Z ⟶ X) : ObjectProperty X.Modules :=
  fun G ↦ SheafOfModules.IsAnnihilatedByKernel
    (RingedSpace.Hom.toRingCatSheafHom i) G

/-- The category of module sheaves annihilated by the ideal of a closed immersion. -/
@[stacks 08KS "category of modules on a closed subspace"]
abbrev AnnihilatedModules (i : Z ⟶ X) := (annihilated i).FullSubcategory

/-- The essential image of pushforward is exactly the property of being annihilated by the
closed-immersion ideal. -/
@[stacks 08KS "(3), essential-image property"]
theorem essImage_eq_annihilated [RingedSpace.IsClosedImmersion i] :
    (pushforward i).essImage = annihilated i := sorry

/-- Pushforward along a closed immersion is an equivalence onto its essential image. -/
@[stacks 08KS "equivalence onto the essential image"]
noncomputable def pushforwardEssImageEquivalence
    [RingedSpace.IsClosedImmersion i] :
    Z.Modules ≌ (pushforward i).EssImageSubcategory :=
  -- Local instance justification (proof-local temporary data): `toEssImage.asEquivalence` consumes fullness through typeclass syntax while the evidence comes from explicit `pushforwardFullyFaithful` data.
  letI : (pushforward i).Full :=
    (pushforwardFullyFaithful (i := i)).full
  -- Local instance justification (proof-local temporary data): `toEssImage.asEquivalence` consumes faithfulness through typeclass syntax while the evidence comes from explicit `pushforwardFullyFaithful` data.
  letI : (pushforward i).Faithful :=
    (pushforwardFullyFaithful (i := i)).faithful
  (pushforward i).toEssImage.asEquivalence

/-- Pushforward identifies modules on the closed subspace with modules on the ambient ringed
space annihilated by the defining ideal. -/
@[stacks 08KS "equivalence with annihilated modules"]
noncomputable def moduleEquivalence [RingedSpace.IsClosedImmersion i] :
    Z.Modules ≌ AnnihilatedModules i :=
  (pushforwardEssImageEquivalence (i := i)).trans
    (ObjectProperty.fullSubcategoryCongr (essImage_eq_annihilated (i := i)))

namespace moduleEquivalence

/-- After forgetting the annihilation property, the forward functor of
`moduleEquivalence` is naturally isomorphic to pushforward. -/
@[stacks 08KS "forward-functor comparison"]
noncomputable def functorCompιIso [RingedSpace.IsClosedImmersion i] :
    (moduleEquivalence (i := i)).functor ⋙ (annihilated i).ι ≅ pushforward i :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforward i).toEssImage
      (ObjectProperty.ιOfLECompιIso (essImage_eq_annihilated (i := i)).le) ≪≫
    Functor.toEssImageCompι (pushforward i)

/-- The forward equivalence sends a module to its pushforward, on underlying objects. -/
@[simp]
theorem functor_obj [RingedSpace.IsClosedImmersion i] (F : Z.Modules) :
    ((moduleEquivalence (i := i)).functor.obj F).obj = (pushforward i).obj F := sorry

/-- The forward equivalence sends a morphism to its pushforward, after forgetting the full
subcategory. -/
@[simp]
theorem functor_map [RingedSpace.IsClosedImmersion i]
    {F G : Z.Modules} (f : F ⟶ G) :
    (annihilated i).ι.map ((moduleEquivalence (i := i)).functor.map f) =
      (functorCompιIso (i := i)).hom.app F ≫
        (pushforward i).map f ≫
          (functorCompιIso (i := i)).inv.app G := sorry

/-- Applying pushforward after the inverse of `moduleEquivalence` is naturally isomorphic to
the inclusion of annihilated modules into all module sheaves on the ambient space. -/
@[stacks 08KS "inverse-functor comparison"]
noncomputable def inverseCompPushforwardIso [RingedSpace.IsClosedImmersion i] :
    (moduleEquivalence (i := i)).inverse ⋙ pushforward i ≅ (annihilated i).ι :=
  (Functor.isoWhiskerLeft (moduleEquivalence (i := i)).inverse
      (functorCompιIso (i := i))).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleEquivalence (i := i)).counitIso
      (annihilated i).ι ≪≫
    (annihilated i).ι.leftUnitor

/-- The pushforward of the inverse image selected by `moduleEquivalence` is canonically
isomorphic to the original annihilated module. -/
@[stacks 08KS "inverse-object comparison"]
noncomputable def inverseObjIso [RingedSpace.IsClosedImmersion i]
    (G : AnnihilatedModules i) :
    (pushforward i).obj ((moduleEquivalence (i := i)).inverse.obj G) ≅ G.obj :=
  (inverseCompPushforwardIso (i := i)).app G

/-- The inverse-object comparison is natural in the annihilated module. -/
@[stacks 08KS "inverse-object comparison, naturality"]
theorem inverseObjIso_naturality [RingedSpace.IsClosedImmersion i]
    {G H : AnnihilatedModules i} (f : G ⟶ H) :
    (pushforward i).map ((moduleEquivalence (i := i)).inverse.map f) ≫
        (inverseObjIso (i := i) H).hom =
      (inverseObjIso (i := i) G).hom ≫ f.hom := sorry

end moduleEquivalence

end AlgebraicGeometry.RingedSpace.IsClosedImmersion
