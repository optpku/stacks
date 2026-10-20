/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback on small etale sites

The small etale site is a morphism-property full subcategory. This leaf gives
its base-change functor directly through Mathlib's generic over-category
pullback construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- Base change along `f` on the small etale sites of schemes. -/
noncomputable abbrev smallEtalePullback (f : T ⟶ S) :
    S.Etale ⥤ T.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

set_option backward.isDefEq.respectTransparency false in
/-- Base change is continuous for the small etale topologies. -/
@[stacks 021I]
instance smallEtalePullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (smallEtalePullback f) S.smallEtaleTopology
      T.smallEtaleTopology := by
  have : PreservesFiniteLimits (smallEtalePullback f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
  have : RepresentablyFlat (smallEtalePullback f) := flat_of_preservesFiniteLimits _
  rw [Functor.isContinuous_iff_coverPreserving]
  constructor
  intro U R hR
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (mem_smallGrothendieckTopology U R).mp hR
  let V (i : 𝒰.I₀) : S.Etale := (𝒰.X i).asOverProp S (hEtale i)
  let g (i : 𝒰.I₀) : V i ⟶ U := (𝒰.f i).asOverProp S
  have hsq (i : 𝒰.I₀) : IsPullback
      (pullback.fst (V i).hom f)
      ((smallEtalePullback f).map (g i)).left
      (𝒰.f i) (pullback.fst U.hom f) := by
    have hfst : ((smallEtalePullback f).map (g i)).left ≫
        pullback.fst U.hom f = pullback.fst (V i).hom f ≫ 𝒰.f i :=
      pullback.lift_fst _ _ _
    have hsnd : ((smallEtalePullback f).map (g i)).left ≫
        pullback.snd U.hom f = pullback.snd (V i).hom f :=
      pullback.lift_snd _ _ _
    apply IsPullback.of_bot _ hfst.symm (IsPullback.of_hasPullback U.hom f)
    rw [hsnd]
    have hg : 𝒰.f i ≫ U.hom = (V i).hom := comp_over (𝒰.f i) S
    rw [hg]
    exact IsPullback.of_hasPullback (V i).hom f
  have hcover : Sieve.ofArrows (fun i ↦ (smallEtalePullback f).obj (V i))
      (fun i ↦ (smallEtalePullback f).map (g i)) ∈ T.smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (pullback.fst U.hom f x)
    obtain ⟨z, _, hz⟩ := exists_preimage_of_isPullback (hsq i) y x hy
    exact Set.mem_iUnion.mpr ⟨i, z, hz⟩
  apply T.smallEtaleTopology.superset_covering _ hcover
  apply Sieve.giGenerate.gc.le_iff_le.mpr
  intro W k hk
  obtain ⟨i⟩ := hk
  exact Sieve.image_mem_functorPushforward _ _ (hle _ _ ⟨i⟩)

/-- The direct image of Type-valued sheaves along small etale base change. -/
noncomputable def smallEtaleDirectImage (f : T ⟶ S) :
    Sheaf T.smallEtaleTopology (Type v) ⥤ Sheaf S.smallEtaleTopology (Type v) :=
  (smallEtalePullback f).sheafPushforwardContinuous
    (Type v) S.smallEtaleTopology T.smallEtaleTopology

/-- Small etale base change presents a morphism of sites. -/
@[stacks 021I]
instance smallEtalePullback_isMorphismOfSites (f : T ⟶ S) :
    IsMorphismOfSites S.smallEtaleTopology T.smallEtaleTopology
      (smallEtalePullback f) where
  toIsContinuous := smallEtalePullback_isContinuous f
  toRepresentablyFlat := by
    have : PreservesFiniteLimits (smallEtalePullback f) :=
      inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
    exact flat_of_preservesFiniteLimits _

/-- Pullback of coefficient-valued sheaves on small etale sites is left adjoint to
continuous direct image. -/
noncomputable def smallEtalePullback_sheafAdjunction (f : T ⟶ S)
    (A : Type v) [Category.{w} A] [HasWeakSheafify T.smallEtaleTopology A]
    [∀ P : S.Etaleᵒᵖ ⥤ A, (smallEtalePullback f).op.HasLeftKanExtension P] :
    (smallEtalePullback f).sheafPullback A S.smallEtaleTopology T.smallEtaleTopology ⊣
      (smallEtalePullback f).sheafPushforwardContinuous
        A S.smallEtaleTopology T.smallEtaleTopology :=
  Functor.sheafAdjunctionContinuous
    (smallEtalePullback f) A S.smallEtaleTopology T.smallEtaleTopology

/-- Sheaf pullback along small etale base change preserves finite limits. -/
instance smallEtalePullback_sheafPullback_preservesFiniteLimits (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology T.smallEtaleTopology) := sorry

/-- Étale inverse image along a flat, locally finitely presented morphism with
geometrically reduced fibres preserves arbitrary products. -/
instance smallEtalePullback_sheafPullback_preservesProducts
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    {J : Type (u + 1)} :
    PreservesLimitsOfShape (Discrete J)
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology X.smallEtaleTopology) := sorry

end AlgebraicGeometry.Scheme
