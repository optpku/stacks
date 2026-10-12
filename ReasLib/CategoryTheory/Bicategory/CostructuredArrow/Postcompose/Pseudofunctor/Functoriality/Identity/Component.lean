/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Basic

/-!
# Components for identity postcomposition of colax costructured arrows

Postcomposition by an identity target `1`-morphism has structural map
`S.hom ≫ 𝟙 _`, so it is not definitionally the identity on colax
costructured-arrow objects. This leaf owns the explicit forward and inverse
components between that object and `S`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X : C}

/-- The forward component from postcomposition by `𝟙 X` to the original
colax costructured arrow.

Its source map is `𝟙 S.left`; its normalized comparison removes
`K.map (𝟙 _)`, then inserts the target right unitor inverse. -/
def postcompose.identity.component.hom
    (S : ColaxCostructuredArrow K X) :
    postcompose.obj (𝟙 X) S ⟶ S :=
  ColaxCostructuredArrow.homMk (K := K) (X := X)
    (𝟙 S.left)
    ((K.mapId S.left).hom ▷ S.hom ≫
      (λ_ S.hom).hom ≫
        (ρ_ S.hom).inv)

/-- The forward identity-postcomposition component has identity source map. -/
@[simp]
theorem postcompose.identity.component.hom.map
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := X)
        (postcompose.identity.component.hom S) =
      𝟙 S.left := sorry

/-- The normalized comparison of the forward identity-postcomposition
component is its explicit map-identity and unitor pasting. -/
@[simp]
theorem postcompose.identity.component.hom.fac
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := X)
        (postcompose.identity.component.hom S) =
      (K.mapId S.left).hom ▷ S.hom ≫
        (λ_ S.hom).hom ≫
          (ρ_ S.hom).inv := sorry

/-- The reverse component from the original colax costructured arrow to its
postcomposition by `𝟙 X`.

Its source map is `𝟙 S.left`; its normalized comparison ends in the forward
target right unitor. -/
def postcompose.identity.component.inv
    (S : ColaxCostructuredArrow K X) :
    S ⟶ postcompose.obj (𝟙 X) S :=
  ColaxCostructuredArrow.homMk (K := K) (X := X)
    (𝟙 S.left)
    ((K.mapId S.left).hom ▷ (S.hom ≫ 𝟙 X) ≫
      (λ_ (S.hom ≫ 𝟙 X)).hom ≫
        (ρ_ S.hom).hom)

/-- The reverse identity-postcomposition component has identity source map. -/
@[simp]
theorem postcompose.identity.component.inv.map
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := X)
        (postcompose.identity.component.inv S) =
      𝟙 S.left := sorry

/-- The normalized comparison of the reverse identity-postcomposition
component is its explicit map-identity and unitor pasting. -/
@[simp]
theorem postcompose.identity.component.inv.fac
    (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.fac (K := K) (X := X)
        (postcompose.identity.component.inv S) =
      (K.mapId S.left).hom ▷ (S.hom ≫ 𝟙 X) ≫
        (λ_ (S.hom ≫ 𝟙 X)).hom ≫
          (ρ_ S.hom).hom := sorry

/- Data and axiom audit (mathlib 4.32):

Both components retain `𝟙 S.left` as their literal source map. Their
normalized comparisons are explicit pastings of `K.mapId`, a left unitor, and
the target right unitor or its inverse. No non-`Prop` data are deferred. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
