/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Projections
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Computations for universal cospan `2`-morphisms

This file records the observable behavior of `mapCospan.map₂`. Comparing the induced apex
`2`-morphism recovers the readable changed-cospan modification, up to the two canonical
universal comparison isomorphisms. The component and projection formulas are consequences
of that complete comparison.

Identity and composition are stated using the ordinary category structure on parallel
cospan transformations, so downstream code can use standard `𝟙` and `≫` notation.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Comparing an induced cospan `2`-morphism recovers the changed-cospan
modification, conjugated by the two universal comparison isomorphisms.

This is the primary specification of `mapCospan.map₂`; it avoids exposing the selected
quasi-inverse used by the bilimit. -/
@[simp]
theorem mapCospan.comparison.map₂
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    (T.toPseudoCone.comparison S.pt).map (mapCospan.map₂ S T Γ) =
      (mapCospan.comparisonIso S T ψ).hom ≫
        changeCospan.modification Γ S ≫
        (mapCospan.comparisonIso S T φ).inv := sorry

/-- At any walking-cospan vertex, the compared induced `2`-morphism is the
corresponding changed-cospan component conjugated by componentwise universal
comparisons. -/
@[simp]
theorem mapCospan.comparison.map₂_app
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (j : LocallyDiscrete Limits.WalkingCospan) :
    ((T.toPseudoCone.comparison S.pt).map
        (mapCospan.map₂ S T Γ)).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapCospan.comparisonIso S T ψ) j).hom ≫
        (changeCospan.modification Γ S).as.app j ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapCospan.comparisonIso S T φ) j).inv := sorry

/-- The induced cospan `2`-morphism commutes with the first projection, up to the
canonical comparison isomorphisms at its source and target. -/
@[simp]
theorem mapCospan.map₂.fst
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    mapCospan.map₂ S T Γ ▷ T.fst =
      (mapCospan.fstIso S T ψ).hom ≫
        S.fst ◁ CospanTransform.Hom.left Γ ≫
        (mapCospan.fstIso S T φ).inv := sorry

/-- The induced cospan `2`-morphism commutes with the second projection, up to the
canonical comparison isomorphisms at its source and target. -/
@[simp]
theorem mapCospan.map₂.snd
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    mapCospan.map₂ S T Γ ▷ T.snd =
      (mapCospan.sndIso S T ψ).hom ≫
        S.snd ◁ CospanTransform.Hom.right Γ ≫
        (mapCospan.sndIso S T φ).inv := sorry

/-- At the central walking-cospan vertex, the induced cospan `2`-morphism is the readable
changed-cospan modification conjugated by the two universal central comparisons. -/
@[simp]
theorem mapCospan.map₂.base
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    mapCospan.map₂ S T Γ ▷ (T.fst ≫ f') =
      (mapCospan.baseIso S T ψ).hom ≫
        (changeCospan.modification Γ S).as.app
          (LocallyDiscrete.mk Limits.WalkingCospan.one) ≫
        (mapCospan.baseIso S T φ).inv := sorry

/-- The cospan map induced by an identity modification carries the identity
`2`-morphism. -/
@[simp]
theorem mapCospan.map₂.id
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    (ψ : CospanTransform f g f' g') :
    mapCospan.map₂ S T (𝟙 ψ) = 𝟙 (mapCospan S T ψ) := sorry

/-- The induced cospan-map construction preserves vertical composition of
modifications. -/
@[simp]
theorem mapCospan.map₂.comp
    (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') [T.IsBilimit]
    {ψ φ χ : CospanTransform f g f' g'}
    (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    mapCospan.map₂ S T (Γ ≫ Δ) =
      mapCospan.map₂ S T Γ ≫ mapCospan.map₂ S T Δ := sorry

end CategoryTheory.Bicategory.PseudoPullbackCone
