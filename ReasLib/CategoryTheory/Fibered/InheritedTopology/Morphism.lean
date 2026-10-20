/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Precoverage
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms between inherited topologies

A cartesian functor between fibered categories preserves the strongly cartesian lifts that
generate their inherited topologies.  The canonical owner accepts an arbitrary precoverage in
`CartesianBasedFunctor.Inherited`; this leaf retains the common `J.toPrecoverage` specialization
for a Grothendieck topology `J`.

## Main declarations

* `CartesianBasedFunctor.inheritedTopology.isContinuous` -- continuity of the total functor.
* `CartesianBasedFunctor.inheritedTopology.isCocontinuous` -- cocontinuity of the total functor.
* `CartesianBasedFunctor.morphismOfTopoiIn` -- the induced morphism of sheaf topoi.
* `CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison` -- the canonical
  comparison with continuous sheaf pushforward.
-/

@[expose] public section

noncomputable section

universe uC vC uS₁ vS₁ uS₂ vS₂ uA

namespace CategoryTheory

open Opposite

namespace CartesianBasedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

namespace inheritedTopology

/-- A cartesian functor is continuous for the inherited topologies of an arbitrary
Grothendieck topology.  No chosen pullbacks for `J.toPrecoverage` are required. -/
@[stacks 06NW]
instance isContinuous
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered] :
    F.toFunctor.IsContinuous (p₁.inheritedTopology J) (p₂.inheritedTopology J) := sorry

/-- A cartesian functor is cocontinuous for the inherited topologies of an arbitrary
Grothendieck topology.  The fibration supplies the required cartesian cover lifts directly. -/
@[stacks 06NW]
instance isCocontinuous
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] :
    F.toFunctor.IsCocontinuous (p₁.inheritedTopology J) (p₂.inheritedTopology J) := sorry

end inheritedTopology

/-- A cartesian functor induces a morphism from the topos of sheaves on the source inherited
topology to the topos of sheaves on the target inherited topology. Its inverse image goes from
target sheaves to source sheaves, and its pushforward goes from source sheaves to target sheaves. -/
@[stacks 06NW]
noncomputable abbrev morphismOfTopoiIn
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (p₂.inheritedTopology J) (p₁.inheritedTopology J) :=
  F.toFunctor.morphismOfTopoiInOfCocontinuous
    (p₁.inheritedTopology J) (p₂.inheritedTopology J)

namespace morphismOfTopoiIn

/-- The direct image of `F.morphismOfTopoiIn J` is the canonical cocontinuous sheaf
pushforward. -/
@[stacks 06NW, simp]
theorem pushforward_eq
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    (F.morphismOfTopoiIn J).pushforward =
      F.toFunctor.sheafPushforwardCocontinuous (Type uA)
        (p₁.inheritedTopology J) (p₂.inheritedTopology J) := sorry

/-- The inverse image of `F.morphismOfTopoiIn J` is the canonical cocontinuous sheaf
pullback. -/
@[stacks 06NW, simp]
theorem inverseImage_eq
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    (F.morphismOfTopoiIn J).inverseImage =
      F.toFunctor.sheafPullbackCocontinuous (Type uA)
        (p₁.inheritedTopology J) (p₂.inheritedTopology J) := sorry

/-- The adjunction stored by `F.morphismOfTopoiIn J` is the canonical adjunction between its
cocontinuous sheaf pullback and pushforward. -/
@[stacks 06NW]
theorem adjunction_eq
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    (F.morphismOfTopoiIn J).adjunction =
      F.toFunctor.sheafPullbackCocontinuousAdjunction
        (p₁.inheritedTopology J) (p₂.inheritedTopology J) := sorry

/-- The canonical comparison from the inverse image induced by a cartesian functor to
continuous sheaf pushforward along its total functor.  This morphism is defined directly;
it does not transport along `inverseImage_eq` or choose an inverse from an `IsIso` proof. -/
@[stacks 06NW "inherited-topology inverse-image comparison"]
noncomputable abbrev inverseImageComparison
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    (F.morphismOfTopoiIn J).inverseImage ⟶
      F.toFunctor.sheafPushforwardContinuous (Type uA)
        (p₁.inheritedTopology J) (p₂.inheritedTopology J) :=
  Functor.CocontinuousPullback.comparison.{uA} F.toFunctor
    (p₁.inheritedTopology J) (p₂.inheritedTopology J)

/-- The inherited inverse-image comparison with both actual sheaf maps supplied. -/
@[stacks 06NW "actual inherited-topology inverse-image isomorphism"]
noncomputable abbrev inverseImageComparisonIso
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    (F.morphismOfTopoiIn J).inverseImage ≅
      F.toFunctor.sheafPushforwardContinuous (Type uA)
        (p₁.inheritedTopology J) (p₂.inheritedTopology J) :=
  Functor.CocontinuousPullback.comparisonIso.{uA} F.toFunctor
    (p₁.inheritedTopology J) (p₂.inheritedTopology J)

/-- The canonical inverse-image comparison for inherited topologies is invertible. -/
@[stacks 06NW]
instance inverseImageComparison.isIso
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P] :
    IsIso (inverseImageComparison F J) :=
  (inverseImageComparisonIso F J).isIso_hom

/-- The canonical objectwise inverse-image comparison at a source object.  It is the value of
`inverseImageComparison`, followed by the direct computation of continuous sheaf pushforward. -/
@[stacks 06NW "objectwise inherited inverse-image comparison"]
noncomputable abbrev inverseImageEvalComparison
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P]
    (G : Sheaf (p₂.inheritedTopology J) (Type uA)) (x : S₁) :
    ((((F.morphismOfTopoiIn J).inverseImage.obj G).obj.obj (op x))) ⟶
      G.obj.obj (op (F.toFunctor.obj x)) :=
  ((Functor.whiskerRight (inverseImageComparison F J)
      (sheafToPresheaf (p₁.inheritedTopology J) (Type uA))).app G).app (op x) ≫
    (F.toFunctor.sheafPushforwardContinuousObjObjIso (Type uA)
      (J := p₁.inheritedTopology J) (K := p₂.inheritedTopology J) G x).hom

/-- The canonical objectwise inverse-image comparison is invertible. -/
@[stacks 06NW]
instance inverseImageEvalComparison.isIso
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P]
    (G : Sheaf (p₂.inheritedTopology J) (Type uA)) (x : S₁) :
    IsIso (inverseImageEvalComparison F J G x) :=
  Iso.isIso_hom
    (((Functor.isoWhiskerRight (inverseImageComparisonIso F J)
        (sheafToPresheaf (p₁.inheritedTopology J) (Type uA))).app G).app (op x) ≪≫
      F.toFunctor.sheafPushforwardContinuousObjObjIso (Type uA)
        (J := p₁.inheritedTopology J) (K := p₂.inheritedTopology J) G x)

namespace inverseImageEvalIso

/-- Evaluate an explicitly supplied inverse of the inherited-topology comparison at a source
object. Unlike `asIso`, this construction never obtains inverse data from an `IsIso` proof. -/
@[stacks 06NW "explicit inherited inverse-image evaluation isomorphism"]
noncomputable abbrev ofComparison
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P]
    (e : Functor.CocontinuousPullback.ComparisonIso.{uA} F.toFunctor
      (p₁.inheritedTopology J) (p₂.inheritedTopology J))
    (G : Sheaf (p₂.inheritedTopology J) (Type uA)) (x : S₁) :
    ((((F.morphismOfTopoiIn J).inverseImage.obj G).obj.obj (op x))) ≅
      G.obj.obj (op (F.toFunctor.obj x)) :=
  ((Functor.isoWhiskerRight e.iso
      (sheafToPresheaf (p₁.inheritedTopology J) (Type uA))).app G).app (op x) ≪≫
    F.toFunctor.sheafPushforwardContinuousObjObjIso (Type uA)
      (J := p₁.inheritedTopology J) (K := p₂.inheritedTopology J) G x

namespace ofComparison

/-- The forward map of the explicitly supplied objectwise inverse-image isomorphism is the
canonical objectwise comparison. -/
@[stacks 06NW]
theorem hom
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P]
    (e : Functor.CocontinuousPullback.ComparisonIso.{uA} F.toFunctor
      (p₁.inheritedTopology J) (p₂.inheritedTopology J))
    (G : Sheaf (p₂.inheritedTopology J) (Type uA)) (x : S₁) :
    (inverseImageEvalIso.ofComparison F J e G x).hom =
      inverseImageEvalComparison F J G x := sorry

/-- The objectwise isomorphism obtained from a canonical comparison inverse is independent of
the supplied inverse choice. -/
@[stacks 06NW]
theorem eq
    (F : CartesianBasedFunctor p₁ p₂) (J : GrothendieckTopology C)
    [p₁.IsFibered] [p₂.IsFibered]
    [HasSheafify (p₁.inheritedTopology J) (Type uA)]
    [HasWeakSheafify (p₂.inheritedTopology J) (Type uA)]
    [∀ P : S₁ᵒᵖ ⥤ Type uA, F.toFunctor.op.HasPointwiseRightKanExtension P]
    (e e' : Functor.CocontinuousPullback.ComparisonIso.{uA} F.toFunctor
      (p₁.inheritedTopology J) (p₂.inheritedTopology J))
    (G : Sheaf (p₂.inheritedTopology J) (Type uA)) (x : S₁) :
    inverseImageEvalIso.ofComparison F J e G x =
      inverseImageEvalIso.ofComparison F J e' G x := sorry

end ofComparison

end inverseImageEvalIso

end morphismOfTopoiIn

end CartesianBasedFunctor

end CategoryTheory

/- Deferred axioms in the bundled topos morphism and comparison are confined to exactness and
naturality proof fields.  The comparison bundle stores its inverse data explicitly and keeps the
forward-map equality as a separate specification field. -/
