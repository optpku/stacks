/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Modification.Construction.Component

/-!
# Strong-transformation assembly for readable change-of-cospan modifications

This file packages the already constructed component and naturality data as a
`Pseudofunctor.StrongTrans`. Its private declarations are only coherence proofs;
the concrete component owner is `Construction.Component`.
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

namespace Implementation

/-- Readable modification naturality is natural in `2`-morphisms of cone
morphisms.
-/
private theorem modificationStrongTrans.naturality
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    ∀ {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v),
      (changeCospan.pseudofunctor φ).map₂ η ▷
            changeCospan.modification.map Γ T ≫
          (changeCospan.modification.naturality Γ v).hom =
        (changeCospan.modification.naturality Γ u).hom ≫
          changeCospan.modification.map Γ S ◁
            (changeCospan.pseudofunctor ψ).map₂ η := sorry

/-- Readable modification naturality is compatible with pseudofunctor identity
comparisons.
-/
private theorem modificationStrongTrans.id
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    ∀ S : PseudoPullbackCone f g,
      (changeCospan.modification.naturality Γ (𝟙 S)).hom ≫
          changeCospan.modification.map Γ S ◁
            ((changeCospan.pseudofunctor ψ).mapId S).hom =
        ((changeCospan.pseudofunctor φ).mapId S).hom ▷
            changeCospan.modification.map Γ S ≫
          (λ_ (changeCospan.modification.map Γ S)).hom ≫
          (ρ_ (changeCospan.modification.map Γ S)).inv := sorry

/-- Readable modification naturality is compatible with pseudofunctor
composition comparisons.
-/
private theorem modificationStrongTrans.comp
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    ∀ {R S T : PseudoPullbackCone f g}
      (u : R ⟶ S) (v : S ⟶ T),
      (changeCospan.modification.naturality Γ (u ≫ v)).hom ≫
          changeCospan.modification.map Γ R ◁
            ((changeCospan.pseudofunctor ψ).mapComp u v).hom =
        ((changeCospan.pseudofunctor φ).mapComp u v).hom ▷
            changeCospan.modification.map Γ T ≫
          (α_ _ _ _).hom ≫
          (changeCospan.pseudofunctor φ).map u ◁
            (changeCospan.modification.naturality Γ v).hom ≫
          (α_ _ _ _).inv ≫
          (changeCospan.modification.naturality Γ u).hom ▷
            (changeCospan.pseudofunctor ψ).map v ≫
          (α_ _ _ _).hom := sorry

end Implementation

/-- The contravariant strong transformation between readable change-of-cospan
pseudofunctors induced by a cospan modification.

For `Γ : ψ ⟶ φ`, its direction is
`changeCospan.pseudofunctor φ ⟶ changeCospan.pseudofunctor ψ`.
-/
def changeCospan.modification.strongTrans
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    Pseudofunctor.StrongTrans
      (changeCospan.pseudofunctor φ)
      (changeCospan.pseudofunctor ψ) where
  app := changeCospan.modification.map Γ
  naturality := changeCospan.modification.naturality Γ
  naturality_naturality :=
    Implementation.modificationStrongTrans.naturality Γ
  naturality_id := Implementation.modificationStrongTrans.id Γ
  naturality_comp := Implementation.modificationStrongTrans.comp Γ

/- Data audit: this leaf adds no new component data; it only packages the
component owner with strong-transformation coherence fields. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
