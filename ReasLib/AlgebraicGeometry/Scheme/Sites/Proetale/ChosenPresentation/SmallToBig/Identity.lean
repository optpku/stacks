/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Identity-base pro-étale relocalization

The inclusion of a chosen small pro-étale site into the big slice induces a
geometric morphism retracting identity-base relocalization. Its direct image
is restriction to the small site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig

variable (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier)

/-- Identity-base relocalization is canonically isomorphic to the inclusion
of the chosen small pro-étale site into the big slice. -/
def relocalizationFunctor_id_iso :
    relocalizationFunctor (𝟙 S) ≅ smallInclusion X S :=
  Functor.isoWhiskerLeft (smallInclusion X S) (Over.mapId S) ≪≫
    Functor.rightUnitor (smallInclusion X S)

/-- Identity-base relocalization is fully faithful. -/
def relocalizationFunctor_id_fullyFaithful :
    (relocalizationFunctor (𝟙 S)).FullyFaithful :=
  (smallObjects X S).fullyFaithfulι.ofIso (relocalizationFunctor_id_iso X S).symm

/-- Identity-base relocalization sends the small-site terminal object to a
terminal object of the chosen big slice. -/
def relocalizationFunctor_id_obj_isTerminal :
    IsTerminal ((relocalizationFunctor (𝟙 S)).obj (smallTerminalObject X S)) :=
  IsTerminal.ofIso (ChosenBigSite.sliceIdentityTerminal X S)
    ((relocalizationFunctor_id_iso X S).app (smallTerminalObject X S)).symm

/-- Identity-base relocalization defines a morphism from the chosen big
pro-étale slice site to the small pro-étale site. -/
theorem identity_isMorphismOfSites :
    IsMorphismOfSites (smallTopology X S) (bigTopology X S)
      (relocalizationFunctor (𝟙 S)) := sorry

/-- Sheaf pullback along identity-base relocalization preserves finite limits. -/
theorem identity_sheafPullback_preservesFiniteLimits
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    PreservesFiniteLimits
      (lowerShriek (𝟙 S)) := sorry

/-- The geometric morphism from the chosen big pro-étale slice topos to the
small pro-étale topos induced by the inclusion of sites. -/
def siteMorphismOfTopoi
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    MorphismOfTopoiIn.{max u v, max u v, u, u, w}
      (smallTopology X S) (bigTopology X S) where
  inverseImageFunctor :=
    ⟨lowerShriek (𝟙 S),
      identity_sheafPullback_preservesFiniteLimits X S⟩
  pushforward :=
    inverseImage (𝟙 S)
  adjunction :=
    lowerShriekAdjunction (𝟙 S)

/-- The inverse image of identity-base relocalization equals the direct image
of the geometric morphism induced by the small-site inclusion. -/
theorem morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasSheafify (smallTopology X S) (Type w)] :
    (morphismOfTopoi (𝟙 S))⁻¹ = (siteMorphismOfTopoi X S).pushforward := rfl

/-- The unit for identity-base relocalization is invertible, by the adjoint
triple and the fully faithful right Kan extension counit. -/
theorem relocalizationFunctor_id_sheafAdjunctionContinuous_unit_isIso
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    IsIso (lowerShriekAdjunction (𝟙 S)).unit := by
  letI := relocalizationFunctor_isContinuous (𝟙 S)
  letI := relocalizationFunctor_isCocontinuous (𝟙 S)
  letI := relocalizationFunctor_op_hasPointwiseRightKanExtension (𝟙 S)
  letI := (relocalizationFunctor_id_fullyFaithful X S).full
  letI := (relocalizationFunctor_id_fullyFaithful X S).faithful
  let t : Adjunction.Triple _ _ _ :=
    ⟨lowerShriekAdjunction (𝟙 S),
      (relocalizationFunctor (𝟙 S)).sheafAdjunctionCocontinuous (Type w)
        (smallTopology X S) (bigTopology X S)⟩
  letI : ∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (relocalizationFunctor (𝟙 S)).op.HasRightKanExtension P := fun P ↦ inferInstance
  letI : ∀ F : Sheaf (smallTopology X S) (Type w), IsIso (t.adj₂.counit.app F) := by
    intro F
    letI : IsIso ((sheafToPresheaf (smallTopology X S) (Type w)).map
        (t.adj₂.counit.app F)) := by
      change IsIso (((relocalizationFunctor (𝟙 S)).sheafAdjunctionCocontinuous
        (Type w) (smallTopology X S) (bigTopology X S)).counit.app F).hom
      rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom,
      Functor.ranAdjunction_counit]
      exact Functor.instIsIsoAppRanCounit_1 (L := (relocalizationFunctor (𝟙 S)).op) (F := F.obj)
    exact isIso_of_reflects_iso _ (sheafToPresheaf (smallTopology X S) (Type w))
  exact t.isIso_unit_iff_isIso_counit.mpr (NatIso.isIso_of_isIso_app _)

/-- The composite of the small-site inclusion morphism and identity-base
relocalization has inverse image canonically isomorphic to the identity. -/
def siteMorphismOfTopoi_comp_morphismOfTopoi_id_iso
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasSheafify (smallTopology X S) (Type w)] :
    (MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S)
      (morphismOfTopoi (𝟙 S)))⁻¹ ≅
      (MorphismOfTopoiIn.id (smallTopology X S))⁻¹ :=
  (@asIso _ _ _ _
    (lowerShriekAdjunction (𝟙 S)).unit
    (relocalizationFunctor_id_sheafAdjunctionContinuous_unit_isIso X S)).symm

/-- Direct image along the small-site inclusion morphism evaluates a big
pro-étale sheaf on the relocalized small-site object. -/
theorem siteMorphismOfTopoi_pushforward_obj_obj
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    (𝒢 : Sheaf (bigTopology X S) (Type w)) (U : smallSite X S) :
    ((siteMorphismOfTopoi X S).pushforward.obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor (𝟙 S)).obj U)) := rfl

end AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig
