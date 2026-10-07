module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.CategoryTheory.Functor.Equivalence.Choice
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Cartesian.Pullback
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Heterogeneous inverse-image action on cartesian Hom categories

This module specializes the neutral `CartesianBasedFunctor.PushforwardHom.mapFunctor` to two
chosen inverse-image stacks.  Source stacks and target stacks retain independent universes.
`pointwiseMapHom` owns the ordinary choice boundary supplied by `Functor.asQuasiInverse`, while
`mapHom` keeps the quasi-inverse explicit for comparison and coherence arguments.
-/

@[expose] public section

universe uC uD vC vD uS vS uS' vS' uT vT uT' vT'

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.Cartesian

variable {u : C ⥤ D}
variable {S : StackOver.{uC, vC, uS, vS} J}
variable {S' : StackOver.{uC, vC, uS', vS'} J}
variable (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT, vT} K u S)
variable (I' : StackOver.InverseImage.{uC, uD, vC, vD, uS', vS', uT', vT'} K u S')

/-- The heterogeneous pushforward Hom functor determined by two chosen inverse-image stacks. -/
@[stacks 04WK "heterogeneous inverse-image pushforward Hom functor"]
noncomputable abbrev pushforwardHom
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    CartesianBasedFunctor I.target.p I'.target.p ⥤
      CartesianBasedFunctor S.p
        (FiberedCategoryOver.pullback u I'.target.toFiberedCategoryOver).p :=
  CartesianBasedFunctor.PushforwardHom.functor
    I.comparison I'.target.toFiberedCategoryOver

/-- The heterogeneous pushforward Hom functor associated to two chosen inverse-image stacks is
canonically an equivalence. -/
@[stacks 04WK "heterogeneous inverse-image pushforward Hom equivalence"]
instance pushforwardHom.isEquivalence
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (pushforwardHom I I').IsEquivalence := sorry

/-- Lemma 8.12.12 (2) (tag 04WS): the heterogeneous inverse-image action associated to an
explicit quasi-inverse of the canonical pushforward Hom functor. -/
@[stacks 04WS "heterogeneous inverse-image Hom action"]
noncomputable abbrev mapHom
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I')) :
    CartesianBasedFunctor S.p S'.p ⥤
      CartesianBasedFunctor I.target.p I'.target.p :=
  CartesianBasedFunctor.PushforwardHom.mapFunctor
    I'.comparison q

namespace mapHom

/-- The inverse-image action postcomposes a source morphism with the second pullback comparison
and applies the selected inverse of the first pushforward Hom functor. -/
@[simp, stacks 04WS "heterogeneous inverse-image action object computation"]
theorem obj
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    (F : CartesianBasedFunctor S.p S'.p) :
    (mapHom I I' q).obj F =
      q.inverse.obj (F.comp (pullbackComparison I')) := sorry

/-- The inverse-image action sends a vertical transformation by right whiskering with the second
pullback comparison and then applying the selected inverse functor. -/
@[simp, stacks 04WS "heterogeneous inverse-image action map computation"]
theorem map
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    {F G : CartesianBasedFunctor S.p S'.p} (η : F ⟶ G) :
    (mapHom I I' q).map η =
      q.inverse.map
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).map η) := sorry

/-- Applying the first pushforward Hom functor after inverse-image transport recovers
postcomposition with the second pullback comparison. -/
@[stacks 04WS "comparison for heterogeneous inverse-image Hom action"]
noncomputable abbrev comparisonIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I')) :
    mapHom I I' q ⋙ pushforwardHom I I' ≅
      CartesianBasedFunctor.postcomp S.p (pullbackComparison I') :=
  CartesianBasedFunctor.PushforwardHom.mapFunctor.comparisonIso
    I'.comparison q

/-- The forward component of the heterogeneous inverse-image comparison is the selected counit at
the postcomposed cartesian morphism. -/
@[simp, stacks 04WS "heterogeneous inverse-image comparison forward component"]
theorem comparisonIso.hom.app
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    (F : CartesianBasedFunctor S.p S'.p) :
    (comparisonIso I I' q).hom.app F =
      q.counitIso.hom.app
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).obj F) := sorry

/-- The inverse component of the heterogeneous inverse-image comparison is the inverse selected
counit at the postcomposed cartesian morphism. -/
@[simp, stacks 04WS "heterogeneous inverse-image comparison inverse component"]
theorem comparisonIso.inv.app
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    (F : CartesianBasedFunctor S.p S'.p) :
    (comparisonIso I I' q).inv.app F =
      q.counitIso.inv.app
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).obj F) := sorry

/-- Two selected quasi-inverses of the canonical pushforward Hom functor induce naturally
isomorphic inverse-image actions. -/
@[stacks 04WS "choice independence of heterogeneous inverse-image Hom action"]
noncomputable abbrev choiceIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q q' : Functor.QuasiInverse (pushforwardHom I I')) :
    mapHom I I' q ≅ mapHom I I' q' :=
  CartesianBasedFunctor.PushforwardHom.mapFunctor.choiceIso
    I'.comparison q q'

/-- The forward component of heterogeneous choice independence is the canonical comparison of the
two selected inverse functors at the postcomposed cartesian morphism. -/
@[simp, stacks 04WS "heterogeneous inverse-image choice forward component"]
theorem choiceIso.hom.app
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q q' : Functor.QuasiInverse (pushforwardHom I I'))
    (F : CartesianBasedFunctor S.p S'.p) :
    (choiceIso I I' q q').hom.app F =
      (q.inverseIso q').hom.app
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).obj F) := sorry

/-- The inverse component of heterogeneous choice independence is the inverse canonical comparison
of the two selected inverse functors at the postcomposed cartesian morphism. -/
@[simp, stacks 04WS "heterogeneous inverse-image choice inverse component"]
theorem choiceIso.inv.app
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q q' : Functor.QuasiInverse (pushforwardHom I I'))
    (F : CartesianBasedFunctor S.p S'.p) :
    (choiceIso I I' q q').inv.app F =
      (q.inverseIso q').inv.app
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).obj F) := sorry

/-- Changing the quasi-inverse preserves the canonical comparison defining the heterogeneous
inverse-image action. -/
@[stacks 04WS "heterogeneous inverse-image choice comparison coherence"]
theorem choiceIso.comparison
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q q' : Functor.QuasiInverse (pushforwardHom I I')) :
    Functor.isoWhiskerRight (choiceIso I I' q q') (pushforwardHom I I') ≪≫
        comparisonIso I I' q' =
      comparisonIso I I' q := sorry

/-- The choice comparison from a heterogeneous inverse-image action to itself is the identity. -/
@[simp, stacks 04WS "heterogeneous inverse-image choice reflexivity"]
theorem choiceIso.refl
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I')) :
    choiceIso I I' q q = Iso.refl (mapHom I I' q) := sorry

/-- Reversing a choice comparison exchanges the two heterogeneous inverse-image actions. -/
@[simp, stacks 04WS "heterogeneous inverse-image choice symmetry"]
theorem choiceIso.symm
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q q' : Functor.QuasiInverse (pushforwardHom I I')) :
    (choiceIso I I' q q').symm = choiceIso I I' q' q := sorry

/-- Choice comparisons between heterogeneous inverse-image actions compose transitively. -/
@[stacks 04WS "heterogeneous inverse-image choice transitivity"]
theorem choiceIso.trans
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q q' q'' : Functor.QuasiInverse (pushforwardHom I I')) :
    choiceIso I I' q q' ≪≫ choiceIso I I' q' q'' = choiceIso I I' q q'' := sorry

/-- Any heterogeneous inverse-image action with the expected pushforward comparison is
canonically isomorphic to the explicit action selected by `q`. -/
@[stacks 04WS "uniqueness of heterogeneous inverse-image Hom action"]
noncomputable abbrev isoOfComparison
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    (L : CartesianBasedFunctor S.p S'.p ⥤
      CartesianBasedFunctor I.target.p I'.target.p)
    (α : L ⋙ pushforwardHom I I' ≅
      CartesianBasedFunctor.postcomp S.p (pullbackComparison I')) :
    L ≅ mapHom I I' q :=
  CartesianBasedFunctor.PushforwardHom.mapFunctor.isoOfComparison
    I'.comparison q L α

/-- The canonical uniqueness isomorphism recovers its supplied pushforward comparison. -/
@[stacks 04WS "heterogeneous inverse-image action uniqueness comparison"]
theorem isoOfComparison.comparison
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    (L : CartesianBasedFunctor S.p S'.p ⥤
      CartesianBasedFunctor I.target.p I'.target.p)
    (α : L ⋙ pushforwardHom I I' ≅
      CartesianBasedFunctor.postcomp S.p (pullbackComparison I')) :
    Functor.isoWhiskerRight (isoOfComparison I I' q L α) (pushforwardHom I I') ≪≫
        comparisonIso I I' q =
      α := sorry

/-- Compatibility with the supplied pushforward comparison characterizes the canonical
uniqueness isomorphism. -/
@[stacks 04WS "heterogeneous inverse-image action uniqueness characterization"]
theorem isoOfComparison.eq_iff
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I'))
    (L : CartesianBasedFunctor S.p S'.p ⥤
      CartesianBasedFunctor I.target.p I'.target.p)
    (α : L ⋙ pushforwardHom I I' ≅
      CartesianBasedFunctor.postcomp S.p (pullbackComparison I'))
    (β : L ≅ mapHom I I' q) :
    β = isoOfComparison I I' q L α ↔
      Functor.isoWhiskerRight β (pushforwardHom I I') ≪≫
          comparisonIso I I' q =
        α := sorry

/-- The uniqueness construction for the canonical comparison is the identity. -/
@[simp, stacks 04WS "heterogeneous inverse-image action canonical uniqueness"]
theorem isoOfComparison.self
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (q : Functor.QuasiInverse (pushforwardHom I I')) :
    isoOfComparison I I' q (mapHom I I' q) (comparisonIso I I' q) =
      Iso.refl (mapHom I I' q) := sorry

/-- Lemma 8.12.12 (2) (tag 04WS): under the invariant finite-limit hypotheses, every explicitly
selected heterogeneous inverse-image Hom action is an equivalence. -/
@[stacks 04WS "heterogeneous inverse-image Hom equivalence"]
instance isEquivalence
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
    (q : Functor.QuasiInverse (pushforwardHom I I')) :
    (mapHom I I' q).IsEquivalence := sorry

end mapHom

/-- Lemma 8.12.12 (2) (tag 04WS): the canonical pointwise inverse-image action on heterogeneous
cartesian Hom categories.  The quasi-inverse of `pushforwardHom I I'` is selected internally, so
ordinary consumers only supply the two inverse-image objects. -/
@[stacks 04WS "canonical pointwise inverse-image Hom action"]
noncomputable def pointwiseMapHom
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    CartesianBasedFunctor S.p S'.p ⥤
      CartesianBasedFunctor I.target.p I'.target.p :=
  mapHom I I' (pushforwardHom I I').asQuasiInverse

namespace pointwiseMapHom

/-- The canonical pointwise inverse-image action applies the selected inverse of
`pushforwardHom I I'` after postcomposition with the second pullback comparison. -/
@[simp, stacks 04WS "canonical inverse-image action object computation"]
theorem obj
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor S.p S'.p) :
    (pointwiseMapHom I I').obj F =
      (pushforwardHom I I').inv.obj (F.comp (pullbackComparison I')) := sorry

/-- The canonical pointwise inverse-image action sends a vertical transformation by
postcomposition with the second pullback comparison followed by the selected inverse functor. -/
@[simp, stacks 04WS "canonical inverse-image action map computation"]
theorem map
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {F G : CartesianBasedFunctor S.p S'.p} (η : F ⟶ G) :
    (pointwiseMapHom I I').map η =
      (pushforwardHom I I').inv.map
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).map η) := sorry

/-- Applying `pushforwardHom I I'` after the canonical pointwise inverse-image action recovers
postcomposition with the second pullback comparison. -/
@[stacks 04WS "canonical pointwise inverse-image Hom comparison"]
noncomputable def comparisonIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    pointwiseMapHom I I' ⋙ pushforwardHom I I' ≅
      CartesianBasedFunctor.postcomp S.p (pullbackComparison I') :=
  mapHom.comparisonIso I I' (pushforwardHom I I').asQuasiInverse

/-- The forward component of the canonical pointwise inverse-image comparison uses the canonical
counit of the pushforward Hom equivalence. -/
@[simp, stacks 04WS "canonical inverse-image comparison forward component"]
theorem comparisonIso.hom.app
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor S.p S'.p) :
    (comparisonIso I I').hom.app F =
      (pushforwardHom I I').asEquivalence.counitIso.hom.app
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).obj F) := sorry

/-- The inverse component of the canonical pointwise inverse-image comparison uses the inverse
canonical counit of the pushforward Hom equivalence. -/
@[simp, stacks 04WS "canonical inverse-image comparison inverse component"]
theorem comparisonIso.inv.app
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (F : CartesianBasedFunctor S.p S'.p) :
    (comparisonIso I I').inv.app F =
      (pushforwardHom I I').asEquivalence.counitIso.inv.app
        ((CartesianBasedFunctor.postcomp S.p (pullbackComparison I')).obj F) := sorry

/-- Lemma 8.12.12 (2) (tag 04WS): under the invariant hypotheses of Sites, Lemma 7.21.8,
the canonical pointwise inverse-image action is an equivalence of heterogeneous cartesian Hom
categories. -/
@[stacks 04WS "canonical pointwise inverse-image Hom equivalence"]
instance isEquivalence
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful] :
    (pointwiseMapHom I I').IsEquivalence := sorry

end pointwiseMapHom

/- Axiom audit: `mapHom` is a transparent specialization of the neutral explicit-choice action;
it introduces no projection, stackification, or quasi-inverse choice. -/

/- Axiom audit: `pointwiseMapHom` selects data only through the shared
`Functor.asQuasiInverse` boundary for the registered `pushforwardHom.isEquivalence` instance.
Its comparison is inherited from the explicit `mapHom` API. -/

end StackOver.InverseImage.Cartesian

end CategoryTheory
