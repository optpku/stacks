module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Algebraic
import StacksCheckRecall

/-!
# Lemma 97.14.2

If `S` is a scheme and `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids
over `(Sch/S)_fppf` such that `𝒳` is representable by an algebraic space, and
`F` is representable by algebraic spaces, surjective, flat, and locally of
finite presentation, then the finite Hilbert stack `H_d(𝒳/𝒴)` is an
algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/- Lemma 97.14.2: if `S` is a scheme and `F : 𝒳 ⟶ 𝒴` is a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf` such that `𝒳` is representable by an
algebraic space, and `F` is representable by algebraic spaces, surjective,
flat, and locally of finite presentation, then the finite Hilbert stack
`H_d(𝒳/𝒴)` is an algebraic stack. The hypotheses `Surjective`, `Flat`, and
`LocallyOfFinitePresentation` each include relative representability by
algebraic spaces. -/
@[stacks 06CI]
#check (AlgebraicGeometry.FiniteHilbertStack.algebraicStack_ofRelativeSpace :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (hX : IsRepresentableByAlgebraicSpace X)
    (d : ℕ) [NeZero d]
    [Groupoids.Hom.Surjective F] [Groupoids.Hom.Flat F]
    [Groupoids.Hom.LocallyOfFinitePresentation F],
    AlgebraicStack (stack F d).toGroupoids)

end AlgebraicGeometry.FiniteHilbertStack
