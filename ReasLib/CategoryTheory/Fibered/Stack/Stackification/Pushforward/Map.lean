/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward.Pullback
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting morphisms between pushforward comparisons

An explicit quasi-inverse of the pushforward Hom functor transports cartesian morphisms between
two source fibred categories to cartesian morphisms between the corresponding targets.  The
construction is universe-polymorphic and independent of any bundled stack presentation.
-/

@[expose] public section

universe uC uD vC vD uX vX uX' vX' uY vY uY' vY'

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace CartesianBasedFunctor.PushforwardHom

variable {u : C ⥤ D} [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable {X : FiberedCategoryOver.{uC, vC, uX, vX} C}
variable {hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X}
variable {Y : FiberedCategoryOver.{uD, vD, uY, vY} D}
variable {i : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X hX).p Y.p}
variable {X' : FiberedCategoryOver.{uC, vC, uX', vX'} C}
variable {hX' : FiberedCategoryOver.Pushforward.ProjectionChoice u X'}
variable {Y' : FiberedCategoryOver.{uD, vD, uY', vY'} D}

/-- Lemma 8.12.12 (2) (tag 04WS), neutral data owner: transport cartesian morphisms through an
explicit quasi-inverse of the heterogeneous pushforward Hom functor. -/
@[stacks 04WS "heterogeneous inverse-image action on Hom categories"]
noncomputable def mapFunctor
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    CartesianBasedFunctor X.p X'.p ⥤ CartesianBasedFunctor Y.p Y'.p :=
  (q.liftFunctor (CartesianBasedFunctor X.p X'.p)).obj
    (CartesianBasedFunctor.postcomp X.p (pullbackComparison i'))

namespace mapFunctor

/-- The transported object is obtained by postcomposing with the second pullback comparison and
then applying the explicitly supplied inverse functor. -/
@[simp, stacks 04WS "heterogeneous Hom transport object computation"]
theorem obj
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (F : CartesianBasedFunctor X.p X'.p) :
    (mapFunctor i' q).obj F =
      q.inverse.obj (F.comp (pullbackComparison i')) := sorry

/-- The transported morphism is right whiskered by the second pullback comparison before the
explicit inverse functor acts on it. -/
@[simp, stacks 04WS "heterogeneous Hom transport map computation"]
theorem map
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    {F G : CartesianBasedFunctor X.p X'.p} (η : F ⟶ G) :
    (mapFunctor i' q).map η =
      q.inverse.map
        ((CartesianBasedFunctor.postcomp X.p
          (pullbackComparison i')).map η) := sorry

/-- Applying the forward pushforward Hom functor after transport recovers postcomposition with
the second pullback comparison. -/
@[stacks 04WS "comparison for heterogeneous inverse-image Hom transport"]
noncomputable def comparisonIso
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    mapFunctor i' q ⋙ PushforwardHom.functor i Y' ≅
      CartesianBasedFunctor.postcomp X.p (pullbackComparison i') :=
  Functor.QuasiInverse.liftFunctor.comparisonIso q
    (CartesianBasedFunctor.postcomp X.p (pullbackComparison i'))

/-- The forward component of the neutral pushforward-Hom comparison is the selected counit at the
postcomposed cartesian functor. -/
@[simp, stacks 04WS "heterogeneous Hom transport comparison forward component"]
theorem comparisonIso.hom.app
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (F : CartesianBasedFunctor X.p X'.p) :
    (comparisonIso i' q).hom.app F =
      q.counitIso.hom.app
        ((CartesianBasedFunctor.postcomp X.p (pullbackComparison i')).obj F) := sorry

/-- The inverse component of the neutral pushforward-Hom comparison is the inverse selected
counit at the postcomposed cartesian functor. -/
@[simp, stacks 04WS "heterogeneous Hom transport comparison inverse component"]
theorem comparisonIso.inv.app
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (F : CartesianBasedFunctor X.p X'.p) :
    (comparisonIso i' q).inv.app F =
      q.counitIso.inv.app
        ((CartesianBasedFunctor.postcomp X.p (pullbackComparison i')).obj F) := sorry

/-- Two explicit quasi-inverses of the same pushforward Hom functor induce naturally isomorphic
transport functors. -/
@[stacks 04WS "choice independence of heterogeneous inverse-image Hom transport"]
noncomputable def choiceIso
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q q' : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    mapFunctor i' q ≅ mapFunctor i' q' :=
  Functor.QuasiInverse.liftFunctor.choiceIso q q'
    (CartesianBasedFunctor.postcomp X.p (pullbackComparison i'))

/-- The forward component of neutral choice independence is the canonical comparison of the two
selected inverse functors at the postcomposed cartesian functor. -/
@[simp, stacks 04WS "heterogeneous Hom transport choice forward component"]
theorem choiceIso.hom.app
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q q' : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (F : CartesianBasedFunctor X.p X'.p) :
    (choiceIso i' q q').hom.app F =
      (q.inverseIso q').hom.app
        ((CartesianBasedFunctor.postcomp X.p (pullbackComparison i')).obj F) := sorry

/-- The inverse component of neutral choice independence is the inverse canonical comparison of
the two selected inverse functors at the postcomposed cartesian functor. -/
@[simp, stacks 04WS "heterogeneous Hom transport choice inverse component"]
theorem choiceIso.inv.app
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q q' : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (F : CartesianBasedFunctor X.p X'.p) :
    (choiceIso i' q q').inv.app F =
      (q.inverseIso q').inv.app
        ((CartesianBasedFunctor.postcomp X.p (pullbackComparison i')).obj F) := sorry

/-- Choice independence preserves the canonical comparison with the forward pushforward Hom
functor. -/
@[stacks 04WS "heterogeneous Hom transport choice coherence"]
theorem choiceIso.comparison
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q q' : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    Functor.isoWhiskerRight (choiceIso i' q q') (PushforwardHom.functor i Y') ≪≫
        comparisonIso i' q' =
      comparisonIso i' q := sorry

/-- The choice comparison from a heterogeneous Hom transport to itself is the identity. -/
@[simp, stacks 04WS "heterogeneous Hom transport choice reflexivity"]
theorem choiceIso.refl
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    choiceIso i' q q = Iso.refl (mapFunctor i' q) := sorry

/-- Reversing a heterogeneous Hom-transport choice comparison exchanges its quasi-inverses. -/
@[simp, stacks 04WS "heterogeneous Hom transport choice symmetry"]
theorem choiceIso.symm
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q q' : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    (choiceIso i' q q').symm = choiceIso i' q' q := sorry

/-- Choice comparisons for heterogeneous Hom transport compose transitively. -/
@[stacks 04WS "heterogeneous Hom transport choice transitivity"]
theorem choiceIso.trans
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q q' q'' : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    choiceIso i' q q' ≪≫ choiceIso i' q' q'' = choiceIso i' q q'' := sorry

/-- Any transport functor with the expected comparison after applying the pushforward Hom
functor is canonically isomorphic to the explicit quasi-inverse lift. -/
@[stacks 04WS "uniqueness of heterogeneous inverse-image Hom transport"]
noncomputable def isoOfComparison
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (L : CartesianBasedFunctor X.p X'.p ⥤ CartesianBasedFunctor Y.p Y'.p)
    (α : L ⋙ PushforwardHom.functor i Y' ≅
      CartesianBasedFunctor.postcomp X.p (pullbackComparison i')) :
    L ≅ mapFunctor i' q :=
  Functor.QuasiInverse.liftFunctor.isoOfComparison q L
    (CartesianBasedFunctor.postcomp X.p (pullbackComparison i')) α

/-- The canonical uniqueness isomorphism recovers the supplied comparison after applying the
pushforward Hom functor. -/
@[stacks 04WS "heterogeneous Hom transport uniqueness coherence"]
theorem isoOfComparison.comparison
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (L : CartesianBasedFunctor X.p X'.p ⥤ CartesianBasedFunctor Y.p Y'.p)
    (α : L ⋙ PushforwardHom.functor i Y' ≅
      CartesianBasedFunctor.postcomp X.p (pullbackComparison i')) :
    Functor.isoWhiskerRight (isoOfComparison i' q L α)
          (PushforwardHom.functor i Y') ≪≫
        comparisonIso i' q =
      α := sorry

/-- Compatibility with the supplied comparison characterizes the canonical uniqueness
isomorphism for heterogeneous Hom transport. -/
@[stacks 04WS "heterogeneous Hom transport uniqueness characterization"]
theorem isoOfComparison.eq_iff
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    (L : CartesianBasedFunctor X.p X'.p ⥤ CartesianBasedFunctor Y.p Y'.p)
    (α : L ⋙ PushforwardHom.functor i Y' ≅
      CartesianBasedFunctor.postcomp X.p (pullbackComparison i'))
    (β : L ≅ mapFunctor i' q) :
    β = isoOfComparison i' q L α ↔
      Functor.isoWhiskerRight β (PushforwardHom.functor i Y') ≪≫
          comparisonIso i' q =
        α := sorry

/-- The uniqueness construction applied to the canonical comparison is the identity. -/
@[simp, stacks 04WS "heterogeneous Hom transport uniqueness reflexivity"]
theorem isoOfComparison.self
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y')) :
    isoOfComparison i' q (mapFunctor i' q) (comparisonIso i' q) =
      Iso.refl (mapFunctor i' q) := sorry

/-- Transport through a pushforward Hom quasi-inverse is an equivalence whenever the second
pullback comparison is an equivalence over the base. -/
@[stacks 04WS "heterogeneous inverse-image Hom equivalence"]
instance isEquivalence
    (i' : CartesianBasedFunctor (FiberedCategoryOver.pushforward u X' hX').p Y'.p)
    (q : Functor.QuasiInverse (PushforwardHom.functor i Y'))
    [hComparison : (pullbackComparison i').toBasedFunctor.IsEquivalence] :
    (mapFunctor i' q).IsEquivalence := sorry

end mapFunctor

/- Axiom audit: both noncanonical inputs, the projection choices and the Hom quasi-inverse, are
explicit.  The functor, comparison, and choice isomorphism reuse the generic quasi-inverse lift. -/

end CartesianBasedFunctor.PushforwardHom

end CategoryTheory
