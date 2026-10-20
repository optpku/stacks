module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.RelativeMap
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open FiberedCategoryOver.Groupoids AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory CategoryTheory.TwoFibreProduct

/- 97.15.0.1: for an object ξ of H_d(X/Y) along a 1-morphism F : X ⟶ Y, the pair
(x, α) induces the 1-morphism
  (Sch/Z)_fppf ⟶ (Sch/U)_fppf ×_{y, Y, F} X
by the 2-fibre-product universal property. This is
`FiniteHilbertStack.relativeMap F ξ` from `GroupoidsOver.slice ξ.Z` to
`relativeApex F ξ`. Choosing an algebraic space X_y over U representing that
2-fibre product, the same data yields
`relativeSpaceHom : ofOver ξ.Z ⟶ X_y` of algebraic spaces over U.
The two displayed diagrams are the commuting triangle of spaces
  ofOver ξ.Z ⟶ X_y over ofOver ξ.U
and the 2-fibre-product square of stacks with apex `relativeApex F ξ`,
first projection `TwoFibreProduct.fst`, second projection `TwoFibreProduct.snd`,
and 2-cell `relativeMapIso`. -/
@[stacks 06CK] #check (AlgebraicGeometry.FiniteHilbertStack.relativeMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : AlgebraicGeometry.FiniteHilbertStack.Obj F d),
    GroupoidsOver.slice ξ.Z ⟶ AlgebraicGeometry.FiniteHilbertStack.relativeApex F ξ)

#check (AlgebraicGeometry.FiniteHilbertStack.relativeMap_fst :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d),
    relativeMap F ξ ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F ≅
      overMap ξ.π)

#check (AlgebraicGeometry.FiniteHilbertStack.relativeMap_snd :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d),
    relativeMap F ξ ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} (YonedaSlice.representative ξ.y) F ≅
      YonedaSlice.representative ξ.x)

#check (AlgebraicGeometry.FiniteHilbertStack.relativeSpaceHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d)
    (Xy : AlgebraicSpace S),
    (relativeApex F ξ ≌ Xy.toGroupoids) → (ofOver ξ.Z ⟶ Xy))

#check (AlgebraicGeometry.FiniteHilbertStack.relativeSpaceHom_comp :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : Obj F d)
    (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
    (e : relativeApex F ξ ≌ Xy.toGroupoids),
    Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (YonedaSlice.representative ξ.y) F) →
    relativeSpaceHom F ξ Xy e ≫ fy = ofOverMap ξ.π)

#check (AlgebraicGeometry.FiniteHilbertStack.relativeSpaceHom_exists :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces F → ∀ {d : ℕ} (ξ : Obj F d),
    ∃ (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
      (e : relativeApex F ξ ≌ Xy.toGroupoids),
      Nonempty
        (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u}
            (YonedaSlice.representative ξ.y) F) ∧
      relativeSpaceHom F ξ Xy e ≫ fy = ofOverMap ξ.π ∧
      toGroupoids.InducesHom (relativeMap F ξ) (ofOverSliceEquiv ξ.Z).symm e
        (relativeSpaceHom F ξ Xy e))

section Presentation

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y)
  {d : ℕ} (ξ : AlgebraicGeometry.FiniteHilbertStack.Obj F d)
  (Xy : AlgebraicSpace S) (fy : Xy ⟶ ofOver ξ.U)
  (e : relativeApex F ξ ≌ Xy.toGroupoids)
  (h : RepresentsBaseChange F (YonedaSlice.representative ξ.y) Xy fy)

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids.InducesHom.recover
    (ofOverSliceEquiv ξ.Z).symm e (relativeMap F ξ) :
  toGroupoids.InducesHom (relativeMap F ξ) (ofOverSliceEquiv ξ.Z).symm e
    (relativeSpaceHom F ξ Xy e))

#check (AlgebraicGeometry.RepresentsBaseChange.projection_triangle h :
  ∃ e : relativeApex F ξ ≌ Xy.toGroupoids,
    Nonempty
      (e.hom ≫ toGroupoids.map fy ≫ (ofOverSliceEquiv ξ.U).hom ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (YonedaSlice.representative ξ.y) F))

end Presentation
