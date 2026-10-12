/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Modification.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Modification.Basic

/-!
# Component data for readable change-of-cospan modification actions

This file owns the readable cone component and its naturality isomorphism. The strong-transformation
coherence that packages these components is in `Construction.StrongTrans`.
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

/-- The readable contravariant cone morphism induced by a modification of
walking-cospan transformations.

Its apex map is the identity. Its comparison first uses the comparison of the
identity morphism of the target readable cone, then applies the conjugated
neutral postcomposition modification.
-/
def changeCospan.modification.map
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    (S : PseudoPullbackCone f g) :
    S.changeCospan φ ⟶ S.changeCospan ψ :=
  PseudoPullbackCone.homMk (𝟙 S.pt)
    (PseudoPullbackCone.fac (𝟙 (S.changeCospan ψ)) ≫
      changeCospan.modification Γ S)

namespace Implementation

/-- The canonical apex-map isomorphism underlying readable modification
naturality. It is the apex isomorphism used by the neutral
`PseudoCone.postcomposeModificationStrongTrans`.
-/
private def modificationNaturality.apexIso
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    PseudoPullbackCone.map
          (changeCospan.map φ u ≫ changeCospan.modification.map Γ T) ≅
      PseudoPullbackCone.map
        (changeCospan.modification.map Γ S ≫ changeCospan.map ψ u) :=
  ρ_ (PseudoPullbackCone.map u) ≪≫
    (λ_ (PseudoPullbackCone.map u)).symm

/-- Compatibility of the forward neutral apex cell with the readable
presentation comparisons.
-/
private theorem modificationNaturality.homComm
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    ((T.changeCospan ψ).toPseudoCone.comparison
          (S.changeCospan φ).pt).map
          (modificationNaturality.apexIso Γ u).hom ≫
        PseudoPullbackCone.fac
          (changeCospan.modification.map Γ S ≫ changeCospan.map ψ u) =
      PseudoPullbackCone.fac
        (changeCospan.map φ u ≫ changeCospan.modification.map Γ T) := sorry

/-- Compatibility of the inverse neutral apex cell with the readable
presentation comparisons.
-/
private theorem modificationNaturality.invComm
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    ((T.changeCospan ψ).toPseudoCone.comparison
          (S.changeCospan φ).pt).map
          (modificationNaturality.apexIso Γ u).inv ≫
        PseudoPullbackCone.fac
          (changeCospan.map φ u ≫ changeCospan.modification.map Γ T) =
      PseudoPullbackCone.fac
        (changeCospan.modification.map Γ S ≫ changeCospan.map ψ u) := sorry

/-- The forward readable `2`-cell underlying modification naturality.
-/
private def modificationNaturality.hom
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    changeCospan.map φ u ≫ changeCospan.modification.map Γ T ⟶
      changeCospan.modification.map Γ S ≫ changeCospan.map ψ u :=
  PseudoPullbackCone.hom₂Mk
    (modificationNaturality.apexIso Γ u).hom
    (modificationNaturality.homComm Γ u)

/-- The inverse readable `2`-cell underlying modification naturality.
-/
private def modificationNaturality.inv
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    changeCospan.modification.map Γ S ≫ changeCospan.map ψ u ⟶
      changeCospan.map φ u ≫ changeCospan.modification.map Γ T :=
  PseudoPullbackCone.hom₂Mk
    (modificationNaturality.apexIso Γ u).inv
    (modificationNaturality.invComm Γ u)

/-- The forward and inverse readable modification-naturality cells compose to
the identity.
-/
private theorem modificationNaturality.homInvId
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    modificationNaturality.hom Γ u ≫
        modificationNaturality.inv Γ u =
      𝟙 (changeCospan.map φ u ≫
        changeCospan.modification.map Γ T) := sorry

/-- The inverse and forward readable modification-naturality cells compose to
the identity.
-/
private theorem modificationNaturality.invHomId
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    modificationNaturality.inv Γ u ≫
        modificationNaturality.hom Γ u =
      𝟙 (changeCospan.modification.map Γ S ≫
        changeCospan.map ψ u) := sorry

end Implementation

/-- The strong naturality isomorphism for readable modification components.

Its apex cell is the canonical unitor comparison underlying
`PseudoCone.postcomposeModificationStrongTrans Γ`; only the surrounding cone
comparisons depend on the readable cospan presentation.
-/
def changeCospan.modification.naturality
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ)
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    changeCospan.map φ u ≫ changeCospan.modification.map Γ T ≅
      changeCospan.modification.map Γ S ≫ changeCospan.map ψ u where
  hom := Implementation.modificationNaturality.hom Γ u
  inv := Implementation.modificationNaturality.inv Γ u
  hom_inv_id := Implementation.modificationNaturality.homInvId Γ u
  inv_hom_id := Implementation.modificationNaturality.invHomId Γ u

/- Data audit: the component owner stores the identity apex map, the readable
comparison modification, and the unitor-based naturality isomorphism explicitly. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
