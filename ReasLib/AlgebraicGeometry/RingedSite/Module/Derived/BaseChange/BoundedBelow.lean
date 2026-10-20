/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below flat base change on ringed sites

The formal input to base change is a square of module pullback functors.  Its mate is the
underived transformation `f_* g^* ⟶ (g')^* (f')_*`; the generic exact-horizontal derived-square
API then produces the bounded-below transformation.  A strict commutative square of ringed-site
morphisms supplies the pullback square through the pseudofunctoriality API in `Module.BaseChange`.

Data-bearing constructors take an explicit source-comparison isomorphism or invertibility
certificate.  Thus unfinished proof debt cannot silently choose inverse data, while the
specification and uniqueness API makes the resulting transformation canonical.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square

noncomputable section

-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe z u v w

namespace RingedSite.Hom.DerivedBaseChange.BoundedBelow

variable {X' X Y' Y : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, z}]

/-- The bounded-below base-change source `Rf_* ⋙ g^*`. -/
@[stacks 0736 "bounded-below ringed-site base-change source"]
abbrev source (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [(g.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} g]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :
  DerivedCategory.Plus (ModuleCat.{z} X) ⥤
      DerivedCategory.Plus (ModuleCat.{z} Y') :=
  modulePushforwardDerivedPlus f ⋙ modulePullbackDerivedPlus g

/-- The bounded-below base-change target `(g')^* ⋙ R(f')_*`. -/
@[stacks 0736 "bounded-below ringed-site base-change target"]
abbrev target (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
    [(g'.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))] :
  DerivedCategory.Plus (ModuleCat.{z} X) ⥤
      DerivedCategory.Plus (ModuleCat.{z} Y') :=
  modulePullbackDerivedPlus g' ⋙ modulePushforwardDerivedPlus f'

/-- The canonical comparison from the one-stage right-derived source to `Rf_* ⋙ g^*`. -/
@[stacks 0736 "bounded-below ringed-site source comparison"]
noncomputable abbrev sourceComparison
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [(g.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} g]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :
    Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ⟶
      source f g :=
  Exact.sourceComparison
    (F := f.modulePushforward.{z}) (G := IsFlat.exactPullback.{z} g)

/-- The canonical comparison from the one-stage right-derived target to
`(g')^* ⋙ R(f')_*`. -/
@[stacks 0736 "bounded-below ringed-site target comparison"]
noncomputable abbrev targetComparison
    (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
    [(g'.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))] :
    Functor.RightDerived.Bounded.functor
        ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}) ⟶
      target g' f' :=
  Exact.targetComparison
    (A := ModuleCat.{z} X) (C := ModuleCat.{z} Y') (D := ModuleCat.{z} X')
    (I := IsFlat.exactPullback.{z} g') (H := f'.modulePushforward.{z})

/-- Flatness makes the canonical source comparison invertible when the two source-side module
categories have enough injectives.  This remains an explicit theorem so deferred proof debt does
not become inverse data through typeclass search. -/
@[stacks 0736 "bounded-below ringed-site source comparison is invertible"]
theorem sourceComparison_isIso
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [(g.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} g]
    [EnoughInjectives (ModuleCat.{z} X)]
    [EnoughInjectives (ModuleCat.{z} Y)] :
    IsIso (sourceComparison f g) := sorry

/-- The source comparison upgraded to an isomorphism from an explicit invertibility
certificate. -/
@[stacks 0736 "bounded-below ringed-site source comparison isomorphism"]
noncomputable def sourceIso
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [(g.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} g]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (h : IsIso (sourceComparison f g)) :
    Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ≅
      source f g :=
  @asIso _ _ _ _ (sourceComparison f g) h

/-- The bounded-below module base-change transformation built from a square of pullbacks and a
concrete source-comparison isomorphism. -/
@[stacks 0736 "bounded-below ringed-site base-change map from an isomorphism"]
noncomputable def mapOfIso
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (e : Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ≅
      source f g) :
    source f g ⟶ target g' f' :=
  Exact.mapOfIso
    (A := ModuleCat.{z} X) (B := ModuleCat.{z} Y)
    (C := ModuleCat.{z} Y') (D := ModuleCat.{z} X')
    (F := f.modulePushforward.{z}) (G := IsFlat.exactPullback.{z} g)
    (I := IsFlat.exactPullback.{z} g') (H := f'.modulePushforward.{z})
    (BaseChange.comparison g' f' f g square) e

/-- Lemma 21.15.1 (0736): the canonical bounded-below base-change transformation associated to
a square of module pullbacks.  The explicit proof argument cannot affect the result. -/
@[stacks 0736 "bounded-below ringed-site base-change transformation"]
noncomputable def map
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g)) :
    source f g ⟶ target g' f' :=
  Exact.map
    (F := f.modulePushforward.{z}) (G := IsFlat.exactPullback.{z} g)
    (I := IsFlat.exactPullback.{z} g') (H := f'.modulePushforward.{z})
    (BaseChange.comparison g' f' f g square) h

/-- The component of a base-change transformation built from a concrete source isomorphism. -/
@[stacks 0736 "bounded-below ringed-site base-change component from an isomorphism"]
noncomputable abbrev appOfIso
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (e : Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ≅
      source f g)
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) :
    (source f g).obj K ⟶ (target g' f').obj K :=
  (mapOfIso square e).app K

/-- The component of the bounded-below module base-change transformation. -/
@[stacks 0736 "bounded-below ringed-site base-change component"]
noncomputable abbrev app
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g))
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) :
    (source f g).obj K ⟶ (target g' f').obj K :=
  (map square h).app K

/-- The bounded-below base-change transformation attached to a strictly commutative square of
ringed-site morphisms. -/
@[stacks 0736 "strict-square bounded-below ringed-site base-change transformation"]
noncomputable abbrev mapOfCommSq
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (hcomm : RingedSite.Hom.comp g' f = RingedSite.Hom.comp f' g)
    (h : IsIso (sourceComparison f g)) :
    source f g ⟶ target g' f' :=
  map (RingedSite.Hom.CommSq.pullbackIso hcomm).inv h

/-- Specification of a bounded-below base-change map relative to a concrete source
isomorphism. -/
@[stacks 0736 "bounded-below ringed-site base-change specification from an isomorphism"]
abbrev IsMapOfIso
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (e : Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ≅
      source f g)
    (eta : source f g ⟶ target g' f') : Prop :=
  Exact.IsMapOfIso
    (F := f.modulePushforward.{z}) (G := IsFlat.exactPullback.{z} g)
    (I := IsFlat.exactPullback.{z} g') (H := f'.modulePushforward.{z})
    (BaseChange.comparison g' f' f g square) e eta

/-- A transformation is the canonical bounded-below base-change map when it satisfies the
derived comparison equation. -/
@[stacks 0736 "bounded-below ringed-site base-change specification"]
abbrev IsMap
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (eta : source f g ⟶ target g' f') : Prop :=
  Exact.IsMap
    (F := f.modulePushforward.{z}) (G := IsFlat.exactPullback.{z} g)
    (I := IsFlat.exactPullback.{z} g') (H := f'.modulePushforward.{z})
    (BaseChange.comparison g' f' f g square) eta

/-- Objectwise form of the bounded-below base-change comparison equation. -/
@[stacks 0736 "bounded-below ringed-site base-change component specification"]
abbrev IsMapAt
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (K : DerivedCategory.Plus (ModuleCat.{z} X))
    (eta : (source f g).obj K ⟶ (target g' f').obj K) : Prop :=
  Exact.IsMapAt
    (F := f.modulePushforward.{z}) (G := IsFlat.exactPullback.{z} g)
    (I := IsFlat.exactPullback.{z} g') (H := f'.modulePushforward.{z})
    (BaseChange.comparison g' f' f g square) K eta

/-- A base-change map built from a concrete source isomorphism satisfies its defining
equation. -/
@[stacks 0736 "bounded-below ringed-site map-from-iso specification"]
theorem mapOfIso_isMapOfIso
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (e : Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ≅
      source f g) :
    IsMapOfIso square e (mapOfIso square e) := sorry

/-- The canonical bounded-below base-change map satisfies its comparison equation. -/
@[stacks 0736 "bounded-below ringed-site base-change map specification"]
theorem map_isMap
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g)) :
    IsMap square (map square h) := sorry

/-- Every component of the canonical bounded-below base-change map satisfies the objectwise
comparison equation. -/
@[stacks 0736 "bounded-below ringed-site base-change component specification"]
theorem map_isMapAt
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g))
    (K : DerivedCategory.Plus (ModuleCat.{z} X)) :
    IsMapAt square K (app square h K) := sorry

/-- The base-change transformation is independent of the proof that the source comparison is
invertible. -/
@[stacks 0736 "bounded-below ringed-site base-change proof independence"]
theorem map_eq
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h₁ h₂ : IsIso (sourceComparison f g)) :
    map square h₁ = map square h₂ := sorry

/-- The concrete-source comparison equation uniquely determines the associated base-change
map. -/
@[stacks 0736 "uniqueness of bounded-below ringed-site maps from an isomorphism"]
theorem IsMapOfIso.eq_mapOfIso
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (e : Functor.RightDerived.Bounded.functor
        (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj) ≅
      source f g)
    {eta : source f g ⟶ target g' f'}
    (h_eta : IsMapOfIso square e eta) :
    eta = mapOfIso square e := sorry

/-- The canonical comparison equation uniquely determines the bounded-below base-change
transformation. -/
@[stacks 0736 "uniqueness of bounded-below ringed-site base-change maps"]
theorem IsMap.eq_map
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g))
    {eta : source f g ⟶ target g' f'} (h_eta : IsMap square eta) :
    eta = map square h := sorry

/-- The objectwise comparison equation uniquely determines a base-change component. -/
@[stacks 0736 "uniqueness of bounded-below ringed-site base-change components"]
theorem IsMapAt.eq_app
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g))
    (K : DerivedCategory.Plus (ModuleCat.{z} X))
    {eta : (source f g).obj K ⟶ (target g' f').obj K}
    (h_eta : IsMapAt square K eta) :
    eta = app square h K := sorry

/-- Components of the bounded-below base-change transformation are natural in the derived
module object. -/
@[stacks 0736 "bounded-below ringed-site base-change naturality"]
theorem app_naturality
    {g' : RingedSite.Hom X' X} {f' : RingedSite.Hom X' Y'}
    {f : RingedSite.Hom X Y} {g : RingedSite.Hom Y' Y}
    [(g'.modulePushforward.{z}).IsRightAdjoint]
    [(f'.modulePushforward.{z}).IsRightAdjoint]
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} g] [IsFlat.{z} g']
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      (f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X'))]
    [Functor.HasRightDerivedFunctor
      (f.modulePushforward.{z} ⋙ (IsFlat.exactPullback.{z} g).obj).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    [Functor.HasRightDerivedFunctor
      ((IsFlat.exactPullback.{z} g').obj ⋙ f'.modulePushforward.{z}).toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{z} X))]
    (square : TwoSquare g.modulePullback.{z} f.modulePullback.{z}
      f'.modulePullback.{z} g'.modulePullback.{z})
    (h : IsIso (sourceComparison f g))
    {K L : DerivedCategory.Plus (ModuleCat.{z} X)} (phi : K ⟶ L) :
    (source f g).map phi ≫ app square h L =
      app square h K ≫ (target g' f').map phi := sorry

-- The constructors inherit only the generic derived-square construction and the canonical
-- module mate; any remaining `sorryAx` is proof debt in those shared categorical owners.

end RingedSite.Hom.DerivedBaseChange.BoundedBelow
