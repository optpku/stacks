/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Lemma 37.78.2 (1): the composition of completely decomposed morphisms of
schemes is completely decomposed. -/
@[stacks 0GTJ] #check (AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed f]
    [AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed g],
    AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed (f ≫ g))

/- Lemma 37.78.2 (2): dependent composition of completely decomposed families
of scheme morphisms is completely decomposed. -/
@[stacks 0GTJ] #check (AlgebraicGeometry.CompletelyDecomposedFamily.comp :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {I : Type v}
    (X : I → AlgebraicGeometry.Scheme.{u}) (π : ∀ i, X i ⟶ T)
    [AlgebraicGeometry.CompletelyDecomposedFamily X π]
    (J : I → Type w) (Y : ∀ i, J i → AlgebraicGeometry.Scheme.{u})
    (ρ : ∀ i, ∀ j : J i, Y i j ⟶ X i)
    [∀ i, AlgebraicGeometry.CompletelyDecomposedFamily (Y i) (ρ i)],
    AlgebraicGeometry.CompletelyDecomposedFamily (fun p : Sigma J ↦ Y p.1 p.2)
      (fun p : Sigma J ↦ ρ p.1 p.2 ≫ π p.1))
