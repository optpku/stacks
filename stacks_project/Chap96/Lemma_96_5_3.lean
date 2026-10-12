/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Lemma_96_5_3_RepresentingFunctor

/-!
# Continuity of the representing functor of a representable 1-morphism

A representable 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf` has a representing functor `u : Y_τ ⥤ X_τ` which is
continuous, defines a morphism of sites `X_τ → Y_τ`, and induces the same
morphism of topoi as `f` itself. Pushforward along `f` evaluates as
`F(u(y))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits Opposite
open FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids.representingFunctor
  (structureMap adjunction pushforwardComparison)
open Functor.LeftAdjoint Functor.ContinuousRightAdjoint
open scoped Bicategory

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable (f : X ⟶ Y) (hf : relativelyRepresentable f) (τ : StandardTopology)

/-- The representing functor `u : Y.total ⥤ X.total` of a relatively
representable 1-morphism `f : X ⟶ Y`, sending each `y` to a chosen
representing object of `x ↦ ((toFunctor f).obj x ⟶ y)`. -/
noncomputable abbrev representingFunctor (f : X ⟶ Y)
    (hf : relativelyRepresentable f) : Y.total ⥤ X.total :=
  FiberedCategoryOver.Groupoids.representingFunctor f
    (relativelyRepresentable.targetYoneda hf)

/-- The source-facing representing functor is the groupoid-fibration
representing functor attached to the target-Hom functors. -/
theorem representingFunctor_def (f : X ⟶ Y) (hf : relativelyRepresentable f) :
    representingFunctor f hf =
      FiberedCategoryOver.Groupoids.representingFunctor f
        (relativelyRepresentable.targetYoneda hf) :=
  sorry

/-- Lemma 96.5.3 (1): Let `f : X ⟶ Y` be a representable 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf`, and let `τ` be one of the
standard topologies Zariski, étale, smooth, syntomic, or fppf. The representing
functor `u : Y.total ⥤ X.total` of `y ↦ ((toFunctor f).obj x ⟶ y)` is
continuous as a functor `Y_τ → X_τ`. -/
@[stacks 06W8]
instance representingFunctor_isContinuous :
    (representingFunctor f hf).IsContinuous
      (Y.associatedTopology τ) (X.associatedTopology τ) :=
  sorry

/-- The representing functor preserves `τ`-covering families. -/
theorem representingFunctor_coverPreserving :
    CoverPreserving (Y.associatedTopology τ) (X.associatedTopology τ)
      (representingFunctor f hf) :=
  sorry

/-- The representing functor is representably flat. -/
instance representingFunctor_representablyFlat :
    RepresentablyFlat (representingFunctor f hf) :=
  sorry

/-- Lemma 96.5.3 (2): the same functor defines a morphism of sites
`X_τ → Y_τ`. -/
@[stacks 06W8]
instance representingFunctor_isMorphismOfSites :
    IsMorphismOfSites (Y.associatedTopology τ) (X.associatedTopology τ)
      (representingFunctor f hf) :=
  sorry

/-- Cocontinuity of `toFunctor f` on associated `τ`-topologies is the
inherited-topology cocontinuity of `toCartesianBasedFunctor f`. -/
instance toFunctor_isCocontinuous :
    (toFunctor f).IsCocontinuous (X.associatedTopology τ) (Y.associatedTopology τ) :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (τ.overTopology S)

/-- For a morphism `β : y' ⟶ y` in `Y`, the square of structure morphisms
`p(u(β))` along `q(β)` is a fibre product. -/
theorem representingFunctor_structureMap_isPullback {y' y : Y.total}
    (β : y' ⟶ y) :
    IsPullback (X.p.map ((representingFunctor f hf).map β))
      (structureMap f (relativelyRepresentable.targetYoneda hf) y')
      (structureMap f (relativelyRepresentable.targetYoneda hf) y)
      (Y.p.map β) :=
  sorry

section morphismOfTopoiIn

variable [HasSheafify (X.associatedTopology τ) (Type (max (u + 1) w))]
variable [∀ P : X.totalᵒᵖ ⥤ Type (max (u + 1) w),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (max (u + 1) w),
    (representingFunctor f hf).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((representingFunctor f hf).sheafPullback (Type (max (u + 1) w))
      (Y.associatedTopology τ) (X.associatedTopology τ))]

/-- The morphism of topoi `Sh(X_τ) ⟶ Sh(Y_τ)` presented by the continuous
representing functor `u : Y_τ → X_τ`. -/
noncomputable def representingFunctor_morphismOfTopoiIn :
    MorphismOfTopoiIn (Y.associatedTopology τ) (X.associatedTopology τ) :=
  (representingFunctor f hf).morphismOfTopoiInOfContinuous
    (Y.associatedTopology τ) (X.associatedTopology τ)

/-- `representingFunctor_morphismOfTopoiIn` is the topos morphism of the
continuous functor `u`. -/
theorem representingFunctor_morphismOfTopoiIn_eq :
    representingFunctor_morphismOfTopoiIn f hf τ =
      (representingFunctor f hf).morphismOfTopoiInOfContinuous
        (Y.associatedTopology τ) (X.associatedTopology τ) :=
  sorry

/-- Lemma 96.5.3 (3): inverse-image half of the same identification of the
morphism of topoi `Sh(X_τ) ⟶ Sh(Y_τ)` induced by `f` in Lemma 96.4.4 with the
morphism of topoi presented by the continuous representing functor `u`. The
sheaf topos is taken in `Type (max (u + 1) w)`, because left Kan extension
along `(representingFunctor f hf).op` does not elaborate at `Type w`. -/
@[stacks 06W8]
noncomputable def representingFunctor_inverseImageIso :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).inverseImage ≅
      (representingFunctor_morphismOfTopoiIn f hf τ).inverseImage :=
  pullbackCocontinuousIsoConstruction (representingFunctor f hf) (toFunctor f)
      (adjunction f (relativelyRepresentable.targetYoneda hf))
      (Type (max (u + 1) w)) ≪≫
    (sheafPullbackConstruction.sheafPullbackIso (representingFunctor f hf)
      (Type (max (u + 1) w)) (Y.associatedTopology τ)
      (X.associatedTopology τ)).symm

/-- `representingFunctor_inverseImageIso` is the cocontinuous Kan-extension
identification composed with `sheafPullbackIso`. -/
theorem representingFunctor_inverseImageIso_eq :
    representingFunctor_inverseImageIso f hf τ =
      pullbackCocontinuousIsoConstruction (representingFunctor f hf) (toFunctor f)
          (adjunction f (relativelyRepresentable.targetYoneda hf))
          (Type (max (u + 1) w)) ≪≫
        (sheafPullbackConstruction.sheafPullbackIso (representingFunctor f hf)
          (Type (max (u + 1) w)) (Y.associatedTopology τ)
          (X.associatedTopology τ)).symm :=
  sorry

/-- Lemma 96.5.3 (4): direct-image half of the identification of the
morphism of topoi `Sh(X_τ) ⟶ Sh(Y_τ)` induced by `f` in Lemma 96.4.4 with the
morphism of topoi presented by the continuous representing functor `u`. The
sheaf topos is taken in `Type (max (u + 1) w)`, because left Kan extension
along `(representingFunctor f hf).op` does not elaborate at `Type w`. -/
@[stacks 06W8]
noncomputable def representingFunctor_pushforwardIso :
    ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).pushforward ≅
      (representingFunctor_morphismOfTopoiIn f hf τ).pushforward :=
  (pushforwardContinuousIso (toFunctor f) (representingFunctor f hf)
      (Type (max (u + 1) w))
      (adjunction f (relativelyRepresentable.targetYoneda hf))).symm

/-- `representingFunctor_pushforwardIso` is the inverse of the continuous
right-adjoint identification of `u.sheafPushforwardContinuous` with
cocontinuous pushforward along `toFunctor f`. -/
theorem representingFunctor_pushforwardIso_eq :
    representingFunctor_pushforwardIso f hf τ =
      (pushforwardContinuousIso (toFunctor f) (representingFunctor f hf)
          (Type (max (u + 1) w))
          (adjunction f (relativelyRepresentable.targetYoneda hf))).symm :=
  sorry

end morphismOfTopoiIn

variable [∀ P : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op P]

/-- Lemma 96.5.3 (5): for any presheaf `F` on `X` and any object `y` of `Y`,
the comparison `f_* F(y) ⟶ F(u(y))` is an isomorphism. -/
@[stacks 06W8]
instance representingFunctor_pushforward_obj (F : X.totalᵒᵖ ⥤ Type w)
    (y : Y.total) :
    IsIso (pushforwardComparison f (relativelyRepresentable.targetYoneda hf) F y) :=
  sorry


end AlgebraicGeometry.GroupoidsOver
