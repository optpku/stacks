/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Computations.Object

/-!
# Map computations for readable change of cospan

This leaf exposes the `1`- and `2`-morphism actions of `changeCospan.pseudofunctor`, together with
their apex and cone-comparison readouts.  Identity and composition comparisons are kept in
`Coherence`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The `1`-morphism action of readable change of cospan is `changeCospan.map`. -/
@[simp]
theorem changeCospan.pseudofunctor.map
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (changeCospan.pseudofunctor ψ).map u =
      changeCospan.map ψ u := sorry
/- Proof strategy: unfold `changeCospan.pseudofunctor` and its explicit prelax core. -/

/-- The apex map of a readable cone morphism is unchanged when its cospan changes. -/
@[simp]
theorem changeCospan.pseudofunctor.map.apex
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map
        ((changeCospan.pseudofunctor ψ).map u) =
      PseudoPullbackCone.map u := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.map` and
`changeCospan.map.apex`. -/

/-- The comparison modification of a changed-cospan cone morphism is `changeCospan.fac`. -/
@[simp]
theorem changeCospan.pseudofunctor.map.fac
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.fac
        ((changeCospan.pseudofunctor ψ).map u) =
      changeCospan.fac ψ u := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.map` and
`changeCospan.map.fac`. -/

/-- The `2`-morphism action of readable change of cospan is `changeCospan.map₂`. -/
@[simp]
theorem changeCospan.pseudofunctor.map₂
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    (changeCospan.pseudofunctor ψ).map₂ η =
      changeCospan.map₂ ψ η := sorry
/- Proof strategy: unfold `changeCospan.pseudofunctor` and its explicit prelax core. -/

/-- The apex cell of a readable cone `2`-morphism is unchanged when its cospan changes. -/
@[simp]
theorem changeCospan.pseudofunctor.map₂.apex
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    PseudoPullbackCone.map₂
        ((changeCospan.pseudofunctor ψ).map₂ η) =
      PseudoPullbackCone.map₂ η := sorry
/- Proof strategy: rewrite with `changeCospan.pseudofunctor.map₂` and
`changeCospan.map₂.apex`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
