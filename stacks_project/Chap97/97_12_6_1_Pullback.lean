module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.TwoFibreProduct

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory CategoryTheory.TwoFibreProduct

/- The canonical Yoneda base change and its projections. -/
#check (AlgebraicGeometry.FiniteHilbertStack.twoFibreProduct :
  ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (FiniteHilbertStack.toGroupoids F d).p.Fiber U), GroupoidsOver S)

#check (AlgebraicGeometry.FiniteHilbertStack.twoFibreProduct.fst :
  ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (FiniteHilbertStack.toGroupoids F d).p.Fiber U),
    FiniteHilbertStack.twoFibreProduct G F d ξ ⟶ GroupoidsOver.slice U)

#check (AlgebraicGeometry.FiniteHilbertStack.twoFibreProduct.snd :
  ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) {U : Over S}
    (ξ : (FiniteHilbertStack.toGroupoids F d).p.Fiber U),
    FiniteHilbertStack.twoFibreProduct G F d ξ ⟶
      FiniteHilbertStack.toGroupoids (G ≫ F) d)
