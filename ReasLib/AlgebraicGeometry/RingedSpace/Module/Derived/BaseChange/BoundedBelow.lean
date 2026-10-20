/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below flat base change on ringed spaces

For a commutative square whose horizontal morphisms are flat, the underived module base-change
transformation induces a canonical natural transformation
`pullback g Rf_* ⟶ R(f')_* (g')^*` on bounded-below derived categories.  The construction is the
generic bounded-below right-derived square map; the geometric file only supplies its four
functors and the underived mate.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.BoundedBaseChange

variable {X X' S S' : RingedSpace.{u}}

/-- The source functor `pullback g Rf_*` of bounded-below flat base change. -/
@[stacks 02N7 "bounded-below flat base-change source"]
abbrev source (f : X ⟶ S) (g : S' ⟶ S) [RingedSpace.Hom.IsFlat g] :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus S'.Modules :=
  Exact.source (pushforward f) (RingedSpace.Hom.IsFlat.exactPullback g)

/-- The target functor `R(f')_* (g')^*` of bounded-below flat base change. -/
@[stacks 02N7 "bounded-below flat base-change target"]
abbrev target (g' : X' ⟶ X) (f' : X' ⟶ S') [RingedSpace.Hom.IsFlat g'] :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus S'.Modules :=
  Exact.target (RingedSpace.Hom.IsFlat.exactPullback g') (pushforward f')

/-- The one-stage/two-stage comparison whose inverse starts flat base change. -/
@[stacks 02N7 "bounded-below flat base-change source comparison"]
noncomputable abbrev sourceComparison
    (f : X ⟶ S) (g : S' ⟶ S) [RingedSpace.Hom.IsFlat g] :
    Functor.RightDerived.Bounded.functor (pushforward f ⋙ pullback g) ⟶ source f g :=
  Exact.sourceComparison
    (F := pushforward f) (G := RingedSpace.Hom.IsFlat.exactPullback g)

/-- The one-stage/two-stage comparison ending flat base change. -/
@[stacks 02N7 "bounded-below flat base-change target comparison"]
noncomputable abbrev targetComparison
    (g' : X' ⟶ X) (f' : X' ⟶ S') [RingedSpace.Hom.IsFlat g'] :
    Functor.RightDerived.Bounded.functor (pullback g' ⋙ pushforward f') ⟶ target g' f' :=
  Exact.targetComparison
    (I := RingedSpace.Hom.IsFlat.exactPullback g') (H := pushforward f')

/-- Flatness supplies the invertibility certificate used by the canonical source comparison.
This named instance keeps downstream constructions from rebuilding local `letI` blocks. -/
@[stacks 02N7 "bounded-below flat base-change source comparison is invertible"]
noncomputable instance sourceComparison_isIso
    (f : X ⟶ S) (g : S' ⟶ S) [RingedSpace.Hom.IsFlat g] :
    IsIso (sourceComparison f g) :=
  Exact.sourceComparison_isIso
    (F := pushforward f) (G := RingedSpace.Hom.IsFlat.exactPullback g)

/-- The canonical isomorphism from the one-stage right-derived source to the two-stage flat
source.  Its construction is centralized in the generic exact-horizontal square API. -/
@[stacks 02N7 "bounded-below flat base-change source isomorphism"]
noncomputable def sourceIso
    (f : X ⟶ S) (g : S' ⟶ S) [RingedSpace.Hom.IsFlat g]
    [h : IsIso (sourceComparison f g)] :
    Functor.RightDerived.Bounded.functor (pushforward f ⋙ pullback g) ≅ source f g :=
  @asIso _ _ _ _ (sourceComparison f g)
    h

/-- The bounded-below flat base-change map built from an explicit source comparison
isomorphism. -/
@[stacks 02N7 "bounded-below flat base-change map from a source isomorphism"]
noncomputable def mapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g)
    (e : Functor.RightDerived.Bounded.functor (pushforward f ⋙ pullback g) ≅ source f g) :
    source f g ⟶ target g' f' :=
  CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact.mapOfIso
    (F := pushforward f) (G := RingedSpace.Hom.IsFlat.exactPullback g)
    (I := RingedSpace.Hom.IsFlat.exactPullback g') (H := pushforward f')
    (BaseChange.map sq) e

/-- Lemma 20.17.1 (02N7): the canonical bounded-below flat base-change natural transformation
for a commutative square of ringed spaces. -/
@[stacks 02N7 "bounded-below flat base-change transformation"]
noncomputable def map
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) :
    source f g ⟶ target g' f' :=
  mapOfIso sq (sourceIso f g)

/-- Lemma 20.17.1 (02N7): the component of the canonical base-change map
`pullback g Rf_* K ⟶ R(f')_* (g')^* K` for a bounded-below derived module object. -/
@[stacks 02N7 "bounded-below flat base-change component"]
noncomputable abbrev app
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus X.Modules) :
    (source f g).obj K ⟶ (target g' f').obj K :=
  (map sq).app K

/-- A natural transformation is the bounded-below flat base-change map when it satisfies the
canonical comparison equation. -/
@[stacks 02N7 "bounded-below flat base-change specification"]
abbrev IsMap
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) (η : source f g ⟶ target g' f') : Prop :=
  CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact.IsMap
    (F := pushforward f) (G := RingedSpace.Hom.IsFlat.exactPullback g)
    (I := RingedSpace.Hom.IsFlat.exactPullback g') (H := pushforward f')
    (BaseChange.map sq) η

/-- Specification relative to a concrete source comparison isomorphism. -/
@[stacks 02N7 "bounded-below flat base-change specification from a source isomorphism"]
abbrev IsMapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g)
    (e : Functor.RightDerived.Bounded.functor (pushforward f ⋙ pullback g) ≅ source f g)
    (η : source f g ⟶ target g' f') : Prop :=
  CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact.IsMapOfIso
    (F := pushforward f) (G := RingedSpace.Hom.IsFlat.exactPullback g)
    (I := RingedSpace.Hom.IsFlat.exactPullback g') (H := pushforward f')
    (BaseChange.map sq) e η

/-- Objectwise form of the bounded-below flat base-change specification. -/
@[stacks 02N7 "bounded-below flat base-change component specification"]
abbrev IsMapAt
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) (K : DerivedCategory.Plus X.Modules)
    (η : (source f g).obj K ⟶ (target g' f').obj K) : Prop :=
  CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact.IsMapAt
    (F := pushforward f) (G := RingedSpace.Hom.IsFlat.exactPullback g)
    (I := RingedSpace.Hom.IsFlat.exactPullback g') (H := pushforward f')
    (BaseChange.map sq) K η

/-- A flat base-change map built from a concrete source comparison satisfies the corresponding
comparison equation. -/
@[stacks 02N7 "bounded-below flat base-change map-from-iso specification"]
theorem mapOfIso_isMapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g)
    (e : Functor.RightDerived.Bounded.functor (pushforward f ⋙ pullback g) ≅ source f g) :
    IsMapOfIso sq e (mapOfIso sq e) := sorry

/-- The canonical bounded-below flat base-change transformation satisfies its comparison
equation. -/
@[stacks 02N7 "bounded-below flat base-change map specification"]
theorem map_isMap
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) : IsMap sq (map sq) := sorry

/-- Every component of the canonical bounded-below flat base-change transformation satisfies
the objectwise comparison equation. -/
@[stacks 02N7 "bounded-below flat base-change component specification"]
theorem map_isMapAt
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) (K : DerivedCategory.Plus X.Modules) :
    IsMapAt sq K (app sq K) := sorry

/-- A transformation satisfying the bounded-below flat base-change equation is the canonical
transformation. -/
@[stacks 02N7 "uniqueness of bounded-below flat base-change maps"]
theorem IsMap.eq_map
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) {η : source f g ⟶ target g' f'}
    (hη : IsMap sq η) : η = map sq := sorry

/-- The comparison equation relative to a concrete source isomorphism determines the associated
flat base-change map uniquely. -/
@[stacks 02N7 "uniqueness of flat base-change maps from a source isomorphism"]
theorem IsMapOfIso.eq_mapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g)
    (e : Functor.RightDerived.Bounded.functor (pushforward f ⋙ pullback g) ≅ source f g)
    {η : source f g ⟶ target g' f'}
    (hη : IsMapOfIso sq e η) :
    η = mapOfIso sq e := sorry

/-- A component satisfying the bounded-below flat base-change equation is the component of the
canonical transformation. -/
@[stacks 02N7 "uniqueness of bounded-below flat base-change components"]
theorem IsMapAt.eq_app
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g) (K : DerivedCategory.Plus X.Modules)
    {η : (source f g).obj K ⟶ (target g' f').obj K}
    (hη : IsMapAt sq K η) : η = app sq K := sorry

/-- Naturality of the canonical bounded-below flat base-change components. -/
@[stacks 02N7 "naturality of bounded-below flat base change"]
theorem app_naturality
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSpace.Hom.IsFlat g] [RingedSpace.Hom.IsFlat g']
    (sq : CommSq g' f' f g)
    {K L : DerivedCategory.Plus X.Modules} (φ : K ⟶ L) :
    (source f g).map φ ≫ app sq L =
      app sq K ≫ (target g' f').map φ := sorry

end AlgebraicGeometry.RingedSpace.Hom.BoundedBaseChange
