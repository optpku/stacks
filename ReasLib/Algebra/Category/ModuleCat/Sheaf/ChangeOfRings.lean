/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.EpiMono
public import ReasLib.Algebra.Category.Ring.Factorization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of rings for sheaves of modules

This file owns the same-site extension/restriction-of-scalars adjunction. It also lifts the
presheaf-level Hom equivalence for a locally surjective map of ring sheaves and packages its
inverse as reusable `Functor.FullyFaithful` data. The neutral `RingCat` range factorization used
by the sheaf epi API is supplied by `ReasLib.Algebra.Category.Ring.Factorization`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z u' v'

namespace SheafOfModules

section Pullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [F.IsContinuous J K]
variable {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}

/-- Pullback of sheaves of modules along a continuous-site coefficient morphism is additive
whenever the corresponding pushforward is a right adjoint. -/
theorem pullback_additive_of_isRightAdjoint
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    [(pushforward.{z} φ).IsRightAdjoint] : (pullback.{z} φ).Additive := sorry

/-- Pullback of sheaves of modules along a continuous-site coefficient morphism is additive.
This is the canonical owner used by complex-valued inverse-image constructions. -/
@[stacks 03D6 "module-sheaf pullback is additive"]
instance pullback_additive
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    [(pushforward.{z} φ).IsRightAdjoint] : (pullback.{z} φ).Additive :=
  pullback_additive_of_isRightAdjoint φ

end Pullback

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R R' : Sheaf J RingCat.{w}}

namespace ChangeOfRings

variable (α : R ⟶ R')

/-- A same-site morphism of ring sheaves in the identity-pushforward form used by the
module-sheaf pullback API. -/
noncomputable abbrev homOverId :
    R ⟶ ((Functor.id C).sheafPushforwardContinuous RingCat.{w} J J).obj R' :=
  α ≫ (Functor.sheafPushforwardContinuousId RingCat.{w} J).inv.app R'

/-- Pushing module sheaves forward along `homOverId α` is canonically the same as
restricting scalars along `α`. -/
noncomputable def pushforwardIso :
    pushforward.{z} (homOverId α) ≅ restrictScalars.{z} α :=
  Iso.refl _

/-- Restriction of scalars is a right adjoint whenever its identity-site presentation is. -/
noncomputable instance restrictScalarsIsRightAdjoint
    [(pushforward.{z} (homOverId α)).IsRightAdjoint] :
    (restrictScalars.{z} α).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardIso α)

/-- Extension of scalars for module sheaves along a same-site map of ring sheaves. -/
noncomputable def extendScalars [(restrictScalars.{z} α).IsRightAdjoint] :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} R' :=
  (restrictScalars.{z} α).leftAdjoint

/-- Extension of scalars for module sheaves is left adjoint to restriction of scalars. -/
@[stacks 03CZ]
noncomputable def extendRestrictAdjunction
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint] :
    extendScalars (R := R) (R' := R') α ⊣
      restrictScalars.{z} (R := R) (R' := R') α :=
  Adjunction.ofIsRightAdjoint
    (restrictScalars.{z} (R := R) (R' := R') α)

/-- Extension of scalars is additive whenever restriction of scalars is a right adjoint. -/
theorem extendScalars_additive_of_isRightAdjoint
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint] :
    (extendScalars (R := R) (R' := R') α).Additive := sorry

/-- Extension of scalars is additive.  Registering this at the generic ring-sheaf level lets
complex-valued APIs infer additivity without rebuilding it for each geometric specialization. -/
@[stacks 03CZ "extension of scalars is additive"]
instance extendScalars_additive
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint] :
    (extendScalars (R := R) (R' := R') α).Additive :=
  extendScalars_additive_of_isRightAdjoint α

/-- The canonical Hom equivalence for extension and restriction of scalars on module sheaves. -/
noncomputable def extendRestrictHomEquiv
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint]
    (M : SheafOfModules.{z} R) (N : SheafOfModules.{z} R') :
    ((extendScalars (R := R) (R' := R') α).obj M ⟶ N) ≃
      (M ⟶ (restrictScalars (R := R) (R' := R') α).obj N) :=
  (extendRestrictAdjunction (R := R) (R' := R') α).homEquiv M N

/-- The extension-restriction Hom equivalence sends a morphism to its composite with the
adjunction unit. -/
theorem extendRestrictHomEquiv_apply
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint]
    (M : SheafOfModules.{z} R) (N : SheafOfModules.{z} R')
    (f : (extendScalars (R := R) (R' := R') α).obj M ⟶ N) :
    extendRestrictHomEquiv (R := R) (R' := R') α M N f =
      (extendRestrictAdjunction (R := R) (R' := R') α).unit.app M ≫
        (restrictScalars (R := R) (R' := R') α).map f := sorry

/-- Any other left adjoint to restriction of scalars is canonically isomorphic to
`extendScalars α`. -/
@[stacks 03CZ "uniqueness of module-sheaf scalar extension"]
noncomputable def extendScalarsIso {F : SheafOfModules.{z} R ⥤ SheafOfModules.{z} R'}
    (adj : F ⊣ restrictScalars.{z} (R := R) (R' := R') α)
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint] :
    F ≅ extendScalars (R := R) (R' := R') α :=
  Adjunction.leftAdjointUniq adj
    (extendRestrictAdjunction (R := R) (R' := R') α)

/-- The forward uniqueness comparison between two scalar-extension functors carries the given
adjunction unit to the canonical extension-restriction unit. -/
@[reassoc, stacks 03CZ "scalar-extension comparison preserves the adjunction unit"]
theorem extendScalarsIso_unit_hom_app
    {F : SheafOfModules.{z} R ⥤ SheafOfModules.{z} R'}
    (adj : F ⊣ restrictScalars.{z} (R := R) (R' := R') α)
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint]
    (M : SheafOfModules.{z} R) :
    adj.unit.app M ≫
        (restrictScalars (R := R) (R' := R') α).map
          ((extendScalarsIso (R := R) (R' := R') α adj).hom.app M) =
      (extendRestrictAdjunction (R := R) (R' := R') α).unit.app M := sorry

/-- The inverse uniqueness comparison carries the canonical extension-restriction unit back to
the unit of the given adjunction. -/
@[reassoc, stacks 03CZ "inverse scalar-extension comparison preserves the adjunction unit"]
theorem extendScalarsIso_unit_inv_app
    {F : SheafOfModules.{z} R ⥤ SheafOfModules.{z} R'}
    (adj : F ⊣ restrictScalars.{z} (R := R) (R' := R') α)
    [(restrictScalars.{z} (R := R) (R' := R') α).IsRightAdjoint]
    (M : SheafOfModules.{z} R) :
    (extendRestrictAdjunction (R := R) (R' := R') α).unit.app M ≫
        (restrictScalars (R := R) (R' := R') α).map
          ((extendScalarsIso (R := R) (R' := R') α adj).inv.app M) =
      adj.unit.app M := sorry

/-- Same-site pullback along `homOverId α` is canonically extension of scalars along `α`. -/
noncomputable def pullbackIso [(pushforward.{z} (homOverId α)).IsRightAdjoint] :
    pullback.{z} (homOverId α) ≅ extendScalars α :=
  extendScalarsIso α
    ((pullbackPushforwardAdjunction (homOverId α)).ofNatIsoRight (pushforwardIso α))

end ChangeOfRings

/-- The forward map on Hom-sets induced by restriction of scalars along a locally surjective
map of sheaves of rings. -/
noncomputable def restrictHomMapOfIsLocallySurjective
    (α : R ⟶ R') {M N : SheafOfModules.{z} R'} [Sheaf.IsLocallySurjective α]
    (f : M ⟶ N) :
    (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom N.isSheaf) f.val⟩

/-- The inverse map on Hom-sets induced by restriction of scalars along a locally surjective
map of sheaves of rings. -/
noncomputable def restrictHomPreimageOfIsLocallySurjective
    (α : R ⟶ R') {M N : SheafOfModules.{z} R'} [Sheaf.IsLocallySurjective α]
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) : M ⟶ N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom N.isSheaf).symm g.val⟩

/-- Taking the preimage of the restricted image of a morphism recovers that morphism. -/
theorem restrictHomPreimage_mapOfIsLocallySurjective
    (α : R ⟶ R') {M N : SheafOfModules.{z} R'} [Sheaf.IsLocallySurjective α]
    (f : M ⟶ N) :
    restrictHomPreimageOfIsLocallySurjective α
      (restrictHomMapOfIsLocallySurjective α f) = f := sorry

/-- Restricting the preimage of a restricted morphism recovers that morphism. -/
theorem restrictHomMap_preimageOfIsLocallySurjective
    (α : R ⟶ R') {M N : SheafOfModules.{z} R'} [Sheaf.IsLocallySurjective α]
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) :
    restrictHomMapOfIsLocallySurjective α
      (restrictHomPreimageOfIsLocallySurjective α g) = g := sorry

/-- Restriction of scalars along a locally surjective map of sheaves of rings induces an
equivalence on Hom-sets of sheaves of modules. -/
noncomputable def restrictHomEquivOfIsLocallySurjective
    (α : R ⟶ R') (M N : SheafOfModules.{z} R') [Sheaf.IsLocallySurjective α] :
    (M ⟶ N) ≃
      ((restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) where
  toFun := restrictHomMapOfIsLocallySurjective α
  invFun := restrictHomPreimageOfIsLocallySurjective α
  left_inv := restrictHomPreimage_mapOfIsLocallySurjective α
  right_inv := restrictHomMap_preimageOfIsLocallySurjective α

/-- The fully faithful preimage followed by restriction recovers a restricted morphism when the
map of sheaves of rings is locally surjective. -/
theorem restrictScalars_map_preimageOfIsLocallySurjective
    (α : R ⟶ R') [Sheaf.IsLocallySurjective α]
    {M N : SheafOfModules.{z} R'}
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) :
    (restrictScalars.{z} α).map
      ((restrictHomEquivOfIsLocallySurjective α M N).symm g) = g := sorry

/-- Restriction followed by the fully faithful preimage recovers an original morphism when the
map of sheaves of rings is locally surjective. -/
theorem restrictScalars_preimage_mapOfIsLocallySurjective
    (α : R ⟶ R') [Sheaf.IsLocallySurjective α]
    {M N : SheafOfModules.{z} R'} (f : M ⟶ N) :
    (restrictHomEquivOfIsLocallySurjective α M N).symm
      ((restrictScalars.{z} α).map f) = f := sorry

/-- Restriction of scalars along a locally surjective map of sheaves of rings is fully
faithful.  This is explicit reusable data rather than a globally registered instance. -/
noncomputable def restrictScalarsFullyFaithfulOfIsLocallySurjective
    (α : R ⟶ R') [hα : Sheaf.IsLocallySurjective α] :
    (restrictScalars.{z} α).FullyFaithful where
  preimage {M N} := (restrictHomEquivOfIsLocallySurjective α M N).symm
  map_preimage := restrictScalars_map_preimageOfIsLocallySurjective α
  preimage_map := restrictScalars_preimage_mapOfIsLocallySurjective α

/-- Under the sheaf-epimorphism/local-surjectivity bridge and a balanced sheaf category,
restriction of scalars along an epimorphism of sheaves of rings is fully faithful. -/
noncomputable def restrictScalarsFullyFaithfulOfEpiOfBalanced
    (α : R ⟶ R') [Epi α]
    [HasSheafify J RingCat.{w}]
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [J.WEqualsLocallyBijective RingCat.{w}]
    [Balanced (Sheaf J RingCat.{w})] :
    (restrictScalars.{z} α).FullyFaithful :=
  restrictScalarsFullyFaithfulOfIsLocallySurjective α
    (hα := (Sheaf.isLocallySurjective_iff_epi' (A := RingCat.{w}) α).2 inferInstance)

/-- The underlying morphism of additive presheaves of a morphism between restrictions of
`R'`-module sheaves.  Its components are definitionally the components of the given morphism. -/
noncomputable def restrictScalarsUnderlyingHom
    (α : R ⟶ R') {M N : SheafOfModules.{z} R'}
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  (PresheafOfModules.toPresheaf R.obj).map g.val

/-- The unchanged underlying additive morphism of a morphism between restrictions along an
epimorphism `R ⟶ R'` respects the original `R'`-module structures.  This is the Prop-valued
compatibility needed to re-bundle it. -/
theorem restrictScalarsHom_smul_of_epi
    (α : R ⟶ R') [Epi α] {M N : SheafOfModules.{z} R'}
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N)
    (X : Cᵒᵖ) (r : R'.obj.obj X) (m : M.val.obj X) :
    (restrictScalarsUnderlyingHom α g).app X (r • m) =
      r • (restrictScalarsUnderlyingHom α g).app X m := sorry

/-- The inverse on morphisms for restriction along an epimorphism of sheaves of rings.
It reuses the given morphism's underlying map of presheaves of abelian groups verbatim;
only its `R'`-linearity is supplied by `restrictScalarsHom_smul_of_epi`. -/
noncomputable def restrictScalarsPreimageOfEpi
    (α : R ⟶ R') [Epi α] {M N : SheafOfModules.{z} R'}
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    (restrictScalarsUnderlyingHom α g)
    (restrictScalarsHom_smul_of_epi α g)⟩

/-- Mapping the re-bundled preimage of a restricted morphism recovers that morphism. -/
@[simp]
theorem restrictScalars_map_preimageOfEpi
    (α : R ⟶ R') [Epi α] {M N : SheafOfModules.{z} R'}
    (g : (restrictScalars.{z} α).obj M ⟶ (restrictScalars.{z} α).obj N) :
    (restrictScalars.{z} α).map (restrictScalarsPreimageOfEpi α g) = g := sorry

/-- Re-bundling the restriction of an `R'`-linear morphism recovers that morphism. -/
@[simp]
theorem restrictScalars_preimage_mapOfEpi
    (α : R ⟶ R') [Epi α] {M N : SheafOfModules.{z} R'} (f : M ⟶ N) :
    restrictScalarsPreimageOfEpi α ((restrictScalars.{z} α).map f) = f := sorry

/-- Restriction of scalars along an epimorphism of sheaves of rings is fully faithful. -/
@[stacks 0930]
noncomputable def restrictScalarsFullyFaithfulOfEpi
    (α : R ⟶ R') [Epi α] : (restrictScalars.{z} α).FullyFaithful where
  preimage := restrictScalarsPreimageOfEpi α
  map_preimage := restrictScalars_map_preimageOfEpi α
  preimage_map := restrictScalars_preimage_mapOfEpi α

end SheafOfModules
