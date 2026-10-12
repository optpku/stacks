/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Proper.Characterization
public import ReasLib.Topology.Sheaf.Derived.BaseChange.BoundedBelow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Proper base change for bounded-below abelian sheaves

This leaf contains only the topological input that makes the generic bounded-below sheaf
base-change comparison invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.BoundedBaseChange

variable {X X' Y Y' : TopCat.{u}}

/-- Theorem 20.18.2 (Proper base change) (09V6): a bounded-below abelian-sheaf base-change
component for a cartesian square is an isomorphism when the original vertical map is proper. -/
@[stacks 09V6 "proper base change for bounded-below abelian sheaves"]
theorem IsMapAt.isIso_of_proper
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hcart : IsPullback g' f' f g) (hf : IsProperMap f)
    (K : D⁺(Ab(X)))
    {η : (source f g).obj K ⟶ (target g' f').obj K}
    (hη : IsMapAt hcart.toCommSq K η) : IsIso η := sorry

/-- A bounded-below abelian-sheaf base-change transformation for a proper cartesian square is a
natural isomorphism. -/
@[stacks 09V6 "functorial proper base change for bounded-below abelian sheaves"]
theorem IsMap.isIso_of_proper
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hcart : IsPullback g' f' f g) (hf : IsProperMap f)
    {η : source f g ⟶ target g' f'}
    (hη : IsMap hcart.toCommSq η) : IsIso η := sorry

/-- The component of a concrete-source base-change map is invertible for a proper cartesian
square when its forward source comparison is the canonical one. -/
@[stacks 09V6 "proper base change component from a source isomorphism"]
theorem appOfIso_isIso_of_proper
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hcart : IsPullback g' f' f g) (hf : IsProperMap f)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    (he : e.hom = sourceComparison f g) (K : D⁺(Ab(X))) :
    IsIso (appOfIso hcart.toCommSq e K) := sorry

/-- A concrete-source base-change transformation is a natural isomorphism for a proper
cartesian square when its forward source comparison is the canonical one. -/
@[stacks 09V6 "proper base change transformation from a source isomorphism"]
theorem mapOfIso_isIso_of_proper
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hcart : IsPullback g' f' f g) (hf : IsProperMap f)
    (e : CategoryTheory.Functor.RightDerived.Bounded.functor
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ≅ source f g)
    (he : e.hom = sourceComparison f g) :
    IsIso (mapOfIso hcart.toCommSq e) := sorry

end TopCat.Sheaf.BoundedBaseChange
