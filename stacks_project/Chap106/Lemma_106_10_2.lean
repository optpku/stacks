module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Compactification
import StacksCheckRecall

/-!
# Compactifying an open of a gerbe by a proper space-to-stack diagram

A separated finite-type morphism from an algebraic stack to a qcqs algebraic
space that is a gerbe over a quasi-compact open admits an open immersion of
algebraic spaces whose image covers that open, with proper structure maps to
the space and the stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.10.2. Let `f : X ⟶ Y` be a morphism from an algebraic stack to an
algebraic space. Let `V ⊂ Y` be an open subspace. Assume `f` is separated and of
finite type, `Y` is quasi-compact and quasi-separated, `V` is quasi-compact, and
`X_V` is a gerbe over `V`. Then there exist algebraic spaces `Zbar`, `Z` and
morphisms `j : Z ⟶ Zbar`, `gBar : Zbar ⟶ Y`, `g : Z ⟶ Y`,
`h : Z.toGroupoids ⟶ X` forming a commutative diagram with `j` an open
immersion, `gBar` and `h` proper, and `|V|` contained in the image of `|g|`.

Here `X_V` is `pullback f V.ι` with structure map `pullbackSnd f V.ι`, the space
triangle is `j ≫ gBar = g`, the stack triangle is a 2-isomorphism
`h ≫ f ≅ AlgebraicSpace.toGroupoids.map g`, and `|V| ⊆ |g|` is
`V.pointsSet ⊆ Set.range (AlgebraicSpace.Points.map g)`. -/
@[stacks 0CQ7] #check
  (AlgebraicGeometry.AlgebraicStack.exists_isOpenImmersion_proper_covering_open :
    ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.Separated f] [AlgebraicStack.FiniteType f]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    [AlgebraicStack.Gerbe (pullbackSnd f V.ι)],
    ∃ (Zbar Z : AlgebraicSpace S) (j : Z ⟶ Zbar) (gBar : Zbar ⟶ Y)
      (g : Z ⟶ Y) (h : Z.toGroupoids ⟶ X),
      AlgebraicSpace.IsOpenImmersion j ∧ AlgebraicSpace.Proper gBar ∧
        AlgebraicStack.Proper h ∧ j ≫ gBar = g ∧
          Nonempty (h ≫ f ≅ AlgebraicSpace.toGroupoids.map g) ∧
            V.pointsSet ⊆ Set.range (AlgebraicSpace.Points.map g))

end AlgebraicGeometry.AlgebraicStack
