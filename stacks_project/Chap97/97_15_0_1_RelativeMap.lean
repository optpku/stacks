module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.RelativeMap

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped Bicategory

#check (AlgebraicGeometry.FiniteHilbertStack.relativeMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : AlgebraicGeometry.FiniteHilbertStack.Obj F d),
    GroupoidsOver.slice ξ.Z ⟶ AlgebraicGeometry.FiniteHilbertStack.relativeApex F ξ)

#check (AlgebraicGeometry.FiniteHilbertStack.relativeSpaceHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ} (ξ : AlgebraicGeometry.FiniteHilbertStack.Obj F d)
    (Xy : AlgebraicSpace S),
    (AlgebraicGeometry.FiniteHilbertStack.relativeApex F ξ ≌ Xy.toGroupoids) →
      (ofOver ξ.Z ⟶ Xy))
