module

import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Representable
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 97.12.6: Let `F : 𝒳 ⟶ 𝒴` and `G : 𝒳' ⟶ 𝒳` be 1-morphisms of stacks
in groupoids over `(Sch/S)_fppf`. If `G` is representable by algebraic spaces,
then the 1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic
spaces.

The source uses positive degree. The established finite Hilbert construction
and the argument using finite local freeness also cover degree zero, so the
shared statement allows every natural degree. -/
@[stacks 05YJ] #check
  (AlgebraicGeometry.FiniteHilbertStack.map.relativelyRepresentableByAlgebraicSpaces :
    ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
      [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
      [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
      [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
      (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ),
      relativelyRepresentableByAlgebraicSpaces G →
        relativelyRepresentableByAlgebraicSpaces (FiniteHilbertStack.map G F d))

#check (AlgebraicGeometry.FiniteHilbertStack.twoFibreProduct.represents :
  ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X'.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ),
    relativelyRepresentableByAlgebraicSpaces G →
      ∀ {U : Over S} (ξ : (FiniteHilbertStack.toGroupoids F d).p.Fiber U),
        ∃ (W : AlgebraicSpace S) (fW : W ⟶ AlgebraicSpace.ofOver U),
          RepresentsBaseChange (FiniteHilbertStack.map G F d)
            (YonedaSlice.representative ξ) W fW)
