/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion

/-!
# Scheme immersions and their locally ringed-space views

Mathlib's scheme predicates remain the canonical owners. This module supplies
the closed-immersion forgetful bridges and the distinct open-then-closed factorization
property used by applications.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem surjectiveOnStalks_of_locallySurjective_structureMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Topology.IsEmbedding f)
    (hsurj : Sheaf.IsLocallySurjective
      (LocallyRingedSpace.Hom.commRingSheafPushforwardMap f.toLRSHom)) :
    SurjectiveOnStalks f := by
  refine ⟨fun x ↦ ?_⟩
  letI := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    CommRingCat hf.isInducing X.presheaf x
  have hstalk := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
    f.toPshHom.c).mp hsurj (f x)
  change Function.Surjective
    ((X.presheaf.stalkPushforward CommRingCat f.base x) ∘
      (TopCat.Presheaf.stalkFunctor CommRingCat (f x)).map f.toPshHom.c)
  exact (ConcreteCategory.bijective_of_isIso _).2.comp hstalk

/-- A scheme morphism is a closed immersion exactly when its locally ringed-space morphism is. -/
@[stacks 01IO "scheme closed immersion bridge"]
theorem isClosedImmersion_iff_toLRSHom_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsClosedImmersion f ↔ LocallyRingedSpace.IsClosedImmersion f.toLRSHom := sorry

/-- A scheme closed immersion remains a closed immersion after forgetting to locally ringed
spaces. -/
@[stacks 01IO "scheme closed immersion forgetful instance"]
instance Scheme.Hom.isClosedImmersion_toLRSHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    LocallyRingedSpace.IsClosedImmersion f.toLRSHom :=
  (isClosedImmersion_iff_toLRSHom_isClosedImmersion f).mp inferInstance

/-- A locally ringed-space closed immersion underlying a scheme morphism is a scheme closed
immersion. -/
@[stacks 01IO "scheme closed immersion converse bridge"]
theorem Scheme.Hom.isClosedImmersion_of_toLRSHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : LocallyRingedSpace.IsClosedImmersion f.toLRSHom) : IsClosedImmersion f := by
  have hclosed : Topology.IsClosedEmbedding f := hf.isClosedEmbedding
  letI := surjectiveOnStalks_of_locallySurjective_structureMap
    f hclosed.isEmbedding hf.toIsLocallySurjective
  exact ⟨hclosed⟩

/-- The canonical closed-subscheme inclusion remains a closed immersion after forgetting to
locally ringed spaces. -/
@[stacks 01IO "closed subscheme forgetful bridge"]
theorem closedSubscheme_ι_toLRSHom_isClosedImmersion
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    LocallyRingedSpace.IsClosedImmersion I.subschemeι.toLRSHom :=
  inferInstance

namespace Scheme.Hom

/-- The structure-sheaf map from a scheme to the pushforward of the source structure sheaf. -/
@[stacks 01LD "structure-sheaf map of a scheme morphism"]
noncomputable abbrev commRingSheafPushforwardMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  LocallyRingedSpace.Hom.commRingSheafPushforwardMap f.toLRSHom

/-- An immersion of schemes is closed exactly when its image is closed. -/
@[stacks 01IQ]
theorem isClosedImmersion_iff_isClosed_range_of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range f) :=
  ⟨fun _ ↦ f.isClosedEmbedding.isClosed_range, IsClosedImmersion.of_isPreimmersion f⟩

end Scheme.Hom

namespace IsClosedImmersion

/-- A closed embedding with a locally surjective
structure-sheaf map is a closed immersion. -/
@[stacks 01LD]
theorem of_isClosedEmbedding_of_isLocallySurjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf_base : Topology.IsClosedEmbedding f)
    (hf_surj : Sheaf.IsLocallySurjective f.commRingSheafPushforwardMap) :
    IsClosedImmersion f := by
  letI := surjectiveOnStalks_of_locallySurjective_structureMap f hf_base.isEmbedding hf_surj
  exact ⟨hf_base⟩

/-- A topological closed embedding together with surjectivity on all stalks is a closed
immersion. -/
@[stacks 01LD "closed immersion from closed embedding and stalk surjectivity"]
theorem of_isClosedEmbedding_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf_base : Topology.IsClosedEmbedding f)
    [SurjectiveOnStalks f] :
    IsClosedImmersion f :=
  ⟨hf_base⟩

end IsClosedImmersion

/-- The morphism property of factoring as an open immersion followed by a closed immersion. -/
@[stacks 01IP "open immersion followed by closed immersion"]
abbrev IsOpenThenClosed : MorphismProperty Scheme.{u} :=
  MorphismProperty.comp IsOpenImmersion
    (fun {X Y} (f : X ⟶ Y) ↦ IsClosedImmersion f)

/-- Explicit factorization criterion for `IsOpenThenClosed`. -/
@[stacks 01IP "open-then-closed immersion factorization criterion"]
theorem isOpenThenClosed_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenThenClosed f ↔
      ∃ (Z : Scheme.{u}) (openMap : X ⟶ Z) (closedMap : Z ⟶ Y),
        IsOpenImmersion openMap ∧ IsClosedImmersion closedMap ∧
          openMap ≫ closedMap = f := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.Z, h.i, h.p, h.hi, h.hp, h.fac⟩
  · rintro ⟨Z, openMap, closedMap, hopen, hclosed, hfac⟩
    exact ⟨{ Z := Z, i := openMap, p := closedMap, hi := hopen, hp := hclosed, fac := hfac }⟩

/-- Some immersion of schemes does not factor as an open immersion followed by a closed
immersion. -/
@[stacks 01IP]
theorem exists_isImmersion_not_isOpenThenClosed :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), IsImmersion f ∧ ¬ IsOpenThenClosed f := sorry

end AlgebraicGeometry
