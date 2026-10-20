/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Descending a pointwise-small injective presentation

The upper injective presentation and the smallness of its target sections are
supplied data. This module transports that presentation to the original carrier
universe; it does not construct the upper target or establish its size bound.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.UniverseLift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})

/-- A lifted morphism descends by applying it to `ULift.up` and then taking `down`. -/
def homDown {M N : SheafOfModules.{u} R}
    (f : (functor R).obj M ⟶ (functor R).obj N) : M ⟶ N where
  val :=
    { app V := ModuleCat.ofHom
        { toFun x := (f.val.app V (ULift.up x)).down
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- Descending a morphism uses the original section as a lifted argument. -/
theorem homDown_apply {M N : SheafOfModules.{u} R}
    (f : (functor R).obj M ⟶ (functor R).obj N) (V : Cᵒᵖ) (x : M.val.obj V) :
    (homDown R f).val.app V x = (f.val.app V (ULift.up x)).down := rfl

/-- The inverse on homs consists of the literal `down`/`up` functions. -/
def fullyFaithfulFunctor : (functor R).FullyFaithful where
  preimage := homDown R
  map_preimage f := by
    ext V x
    exact ULift.up_down (f.val.app V x)
  preimage_map f := by
    ext V x
    rfl

instance : (functor R).Full := (fullyFaithfulFunctor R).full

instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

/-- A monomorphism remains pointwise injective after lifting its carriers. -/
instance : (functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    constructor
    intro P g h e
    ext V x
    apply ULift.ext
    haveI : Mono ((SheafOfModules.evaluation R V).map f) :=
      Functor.map_mono _ f
    have hinj : Function.Injective (f.val.app V) :=
      (ModuleCat.mono_iff_injective ((SheafOfModules.evaluation R V).map f)).mp
        (Functor.map_mono _ f)
    apply hinj
    have he := congrArg (fun q => q.val.app V x) e
    exact congrArg ULift.down he

variable (N : SheafOfModules.{u + 1} (ring R))

/-- Restrict the upper action along the explicit inclusion of the coefficient ring. -/
abbrev lowerScalarAction (V : Cᵒᵖ) : Module (R.obj.obj V) (N.val.obj V) :=
  Module.compHom (N.val.obj V)
    (ULift.ringEquiv.symm.toRingHom : R.obj.obj V →+* (ring R).obj.obj V)

/-- The small module carrier has its actual transported action and restrictions. -/
def shrinkPresheaf [∀ V, Small.{u} (N.val.obj V)] : PresheafOfModules.{u} R.obj := by
  letI : ∀ V, Module (R.obj.obj V) (N.val.obj V) := lowerScalarAction R N
  exact
    { obj V := ModuleCat.of (R.obj.obj V) (Shrink.{u} (N.val.obj V))
      map {V W} f := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
          (ModuleCat.of (R.obj.obj W) (Shrink.{u} (N.val.obj W))))
        { toFun x := equivShrink.{u} (N.val.obj W)
            (N.val.map f ((equivShrink.{u} (N.val.obj V)).symm x))
          map_add' := by sorry
          map_smul' := by sorry }
      map_id := by sorry
      map_comp := by sorry }

/-- Both directions of the underlying additive comparison are given by the small-carrier equivalence. -/
def shrinkPresheafIso [∀ V, Small.{u} (N.val.obj V)] :
    (shrinkPresheaf R N).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅ N.val.presheaf :=
  NatIso.ofComponents (fun V =>
    (AddEquiv.ulift.trans (Shrink.addEquiv (α := N.val.obj V))).toAddCommGrpIso)
    (by sorry)

/-- Sheafness is transported through the explicit additive comparison. -/
theorem shrinkPresheaf_isSheaf [∀ V, Small.{u} (N.val.obj V)] :
    Presheaf.IsSheaf J (shrinkPresheaf R N).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{u + 1, u}
  exact (Presheaf.isSheaf_of_iso_iff (shrinkPresheafIso R N)).mpr N.isSheaf

/-- Shrink a supplied upper sheaf with genuinely small sections. -/
def shrinkObj [∀ V, Small.{u} (N.val.obj V)] : SheafOfModules.{u} R :=
  ⟨shrinkPresheaf R N, shrinkPresheaf_isSheaf R N⟩

/-- Lifting the small target recovers the given target, using explicit maps in both directions. -/
def shrinkIso [∀ V, Small.{u} (N.val.obj V)] :
    (functor R).obj (shrinkObj R N) ≅ N where
  hom :=
    { val :=
        { app V := ModuleCat.ofHom
            { toFun x := (equivShrink.{u} (N.val.obj V)).symm x.down
              map_add' := by sorry
              map_smul' := by sorry }
          naturality := by sorry } }
  inv :=
    { val :=
        { app V := ModuleCat.ofHom
            { toFun x := ULift.up (equivShrink.{u} (N.val.obj V) x)
              map_add' := by sorry
              map_smul' := by sorry }
          naturality := by sorry } }
  hom_inv_id := by
    ext V x
    change ULift.up (equivShrink.{u} (N.val.obj V)
      ((equivShrink.{u} (N.val.obj V)).symm x.down)) = x
    rw [Equiv.apply_symm_apply]
    exact ULift.up_down x
  inv_hom_id := by
    ext V x
    exact Equiv.symm_apply_apply _ x

/-- The descended target's carrier is the genuine `Shrink` of the supplied target. -/
theorem shrinkObj_carrier [∀ V, Small.{u} (N.val.obj V)] (V : Cᵒᵖ) :
    ((shrinkObj R N).val.obj V : Type u) = Shrink.{u} (N.val.obj V) := rfl

/-- Restriction is conjugated by the supplied equivalences of section carriers. -/
theorem shrinkObj_map [∀ V, Small.{u} (N.val.obj V)]
    {V W : Cᵒᵖ} (f : V ⟶ W) (x : (shrinkObj R N).val.obj V) :
    (shrinkObj R N).val.map f x = equivShrink.{u} (N.val.obj W)
      (N.val.map f ((equivShrink.{u} (N.val.obj V)).symm x)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The lower scalar action is the transported action of the lifted scalar. -/
theorem shrinkObj_smul [∀ V, Small.{u} (N.val.obj V)] (V : Cᵒᵖ)
    (r : R.obj.obj V) (x : (shrinkObj R N).val.obj V) :
    r • x = equivShrink.{u} (N.val.obj V)
      ((ULift.up r : (ring R).obj.obj V) •
        (equivShrink.{u} (N.val.obj V)).symm x) := rfl

/-- The upper comparison sends a lifted small section through the supplied carrier equivalence. -/
theorem shrinkIso_hom_up [∀ V, Small.{u} (N.val.obj V)] (V : Cᵒᵖ)
    (x : (shrinkObj R N).val.obj V) :
    (shrinkIso R N).hom.val.app V (ULift.up x) =
      (equivShrink.{u} (N.val.obj V)).symm x := rfl

/-- The reverse comparison applies the supplied shrinking equivalence and then lifts. -/
theorem shrinkIso_inv_apply [∀ V, Small.{u} (N.val.obj V)] (V : Cᵒᵖ)
    (x : N.val.obj V) :
    (shrinkIso R N).inv.val.app V x = ULift.up (equivShrink.{u} (N.val.obj V) x) := rfl

variable {R} {M : SheafOfModules.{u} R}

/-- Descend the given upper embedding to the small target by an explicit hom preimage. -/
def descendEmbedding (I : InjectivePresentation ((functor R).obj M))
    [∀ V, Small.{u} (I.J.val.obj V)] : M ⟶ shrinkObj R I.J :=
  homDown R (I.f ≫ (shrinkIso R I.J).inv)

/-- The embedding is computed by shrinking the value of the given upper embedding. -/
theorem descendEmbedding_apply (I : InjectivePresentation ((functor R).obj M))
    [∀ V, Small.{u} (I.J.val.obj V)] (V : Cᵒᵖ) (x : M.val.obj V) :
    (descendEmbedding I).val.app V x =
      equivShrink.{u} (I.J.val.obj V) (I.f.val.app V (ULift.up x)) := rfl

/-- A genuine pointwise-small upper injective presentation yields a lower presentation. -/
def descendInjectivePresentation (I : InjectivePresentation ((functor R).obj M))
    [∀ V, Small.{u} (I.J.val.obj V)] : InjectivePresentation M where
  J := shrinkObj R I.J
  injective := (functor R).injective_of_map_injective
    (Injective.of_iso (shrinkIso R I.J).symm I.injective)
  f := descendEmbedding I
  mono := by
    apply Functor.mono_of_mono_map (functor R)
    change Mono ((functor R).map
      ((fullyFaithfulFunctor R).preimage (I.f ≫ (shrinkIso R I.J).inv)))
    rw [(fullyFaithfulFunctor R).map_preimage]
    infer_instance

end SheafOfModules.UniverseLift
