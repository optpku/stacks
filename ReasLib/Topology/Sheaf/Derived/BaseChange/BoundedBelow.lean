module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaf.Derived.Basic
public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Sheaves.Abelian
public import ReasLib.Topology.Sheaves.BaseChange
public import ReasLib.Topology.Sheaves.Pullback.Exactness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below base change for abelian sheaves

Inverse image of abelian sheaves is exact, so a direct-image/inverse-image square is a direct
specialization of the generic exact-horizontal right-derived square.  The public API exposes the
comparison equation and accepts concrete source isomorphisms when constructing data; it does not
select inverses from unfinished invertibility proofs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.BoundedBaseChange

open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square

variable {X X' Y Y' : TopCat.{u}}

/-- The bounded-below base-change source `Rf_* ⋙ g⁻¹` for abelian sheaves. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change source"]
abbrev source (f : X ⟶ Y) (g : Y' ⟶ Y) :
    D⁺(Ab(X)) ⥤ D⁺(Ab(Y')) :=
  Exact.source (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (TopCat.Sheaf.exactPullback g)

/-- The bounded-below base-change target `(g')⁻¹ ⋙ R(f')_*` for abelian sheaves. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change target"]
abbrev target (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    D⁺(Ab(X)) ⥤ D⁺(Ab(Y')) :=
  Exact.target (TopCat.Sheaf.exactPullback g')
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')

/-- The canonical comparison from the one-stage right-derived source to the two-stage source. -/
@[stacks 09V6 "bounded-below abelian-sheaf source comparison"]
noncomputable abbrev sourceComparison (f : X ⟶ Y) (g : Y' ⟶ Y) :
    CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ⟶
      source f g :=
  Exact.sourceComparison
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (G := TopCat.Sheaf.exactPullback g)

/-- The canonical comparison from the one-stage right-derived target to the two-stage target. -/
@[stacks 09V6 "bounded-below abelian-sheaf target comparison"]
noncomputable abbrev targetComparison (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} g' ⋙
          TopCat.Sheaf.pushforward AddCommGrpCat.{u} f') ⟶
      target g' f' :=
  Exact.targetComparison
    (I := TopCat.Sheaf.exactPullback g')
    (H := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')

/-- The bounded-below base-change transformation constructed from a concrete identification of
the one-stage derived source with the two-stage source. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change map from an isomorphism"]
noncomputable def mapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g) :
    source f g ⟶ target g' f' :=
  Exact.mapOfIso
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (G := TopCat.Sheaf.exactPullback g)
    (I := TopCat.Sheaf.exactPullback g')
    (H := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.BaseChange.map AddCommGrpCat.{u} sq) e

/-- The component of `mapOfIso` at a bounded-below derived abelian sheaf. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change component from an isomorphism"]
noncomputable abbrev appOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    (K : D⁺(Ab(X))) :
    (source f g).obj K ⟶ (target g' f').obj K :=
  (mapOfIso sq e).app K

/-- Specification of a bounded-below abelian-sheaf base-change map relative to a concrete
identification of the one-stage derived source. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change specification from an isomorphism"]
abbrev IsMapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    (η : source f g ⟶ target g' f') : Prop :=
  Exact.IsMapOfIso
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (G := TopCat.Sheaf.exactPullback g)
    (I := TopCat.Sheaf.exactPullback g')
    (H := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.BaseChange.map AddCommGrpCat.{u} sq) e η

/-- A transformation is a bounded-below base-change map when it satisfies the canonical derived
comparison equation. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change specification"]
abbrev IsMap
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (η : source f g ⟶ target g' f') : Prop :=
  Exact.IsMap
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (G := TopCat.Sheaf.exactPullback g)
    (I := TopCat.Sheaf.exactPullback g')
    (H := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.BaseChange.map AddCommGrpCat.{u} sq) η

/-- Objectwise form of the bounded-below abelian-sheaf base-change comparison equation. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change component specification"]
abbrev IsMapAt
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (K : D⁺(Ab(X)))
    (η : (source f g).obj K ⟶ (target g' f').obj K) : Prop :=
  Exact.IsMapAt
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (G := TopCat.Sheaf.exactPullback g)
    (I := TopCat.Sheaf.exactPullback g')
    (H := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (TopCat.Sheaf.BaseChange.map AddCommGrpCat.{u} sq) K η

/-- The base-change map built from a concrete source isomorphism satisfies its concrete-source
comparison equation. -/
@[stacks 09V6 "bounded-below abelian-sheaf map-from-iso specification"]
theorem mapOfIso_isMapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g) :
    IsMapOfIso sq e (mapOfIso sq e) := sorry

/-- A concrete-source base-change map is canonical when the chosen isomorphism has the canonical
source comparison as its forward map. -/
@[stacks 09V6 "bounded-below abelian-sheaf map-from-iso canonical specification"]
theorem mapOfIso_isMap
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    (he : e.hom = sourceComparison f g) :
    IsMap sq (mapOfIso sq e) := sorry

/-- Every component of a concrete-source base-change map with canonical forward comparison
satisfies the canonical objectwise equation. -/
@[stacks 09V6 "bounded-below abelian-sheaf map-from-iso component specification"]
theorem mapOfIso_isMapAt
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    (he : e.hom = sourceComparison f g) (K : D⁺(Ab(X))) :
    IsMapAt sq K (appOfIso sq e K) := sorry

/-- The concrete-source comparison equation determines the corresponding bounded-below
base-change map uniquely. -/
@[stacks 09V6 "uniqueness of bounded-below abelian-sheaf maps from an isomorphism"]
theorem IsMapOfIso.eq_mapOfIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    {η : source f g ⟶ target g' f'} (hη : IsMapOfIso sq e η) :
    η = mapOfIso sq e := sorry

/-- A transformation satisfying the canonical comparison equation is objectwise a base-change
map. -/
@[stacks 09V6 "bounded-below abelian-sheaf base-change components"]
theorem IsMap.isMapAt
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) {η : source f g ⟶ target g' f'}
    (hη : IsMap sq η) (K : D⁺(Ab(X))) :
    IsMapAt sq K (η.app K) := sorry

end TopCat.Sheaf.BoundedBaseChange
