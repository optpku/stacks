module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KeelMori.Proper
import StacksCheckRecall

/-!
# Properness of Keel–Mori moduli spaces

If an algebraic stack of finite inertia maps properly to a locally Noetherian
algebraic space, then a uniform categorical moduli space induces a proper
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.14.3. Let `p : X ⟶ Y.toGroupoids` be a morphism from an algebraic
stack to an algebraic space. Assume the inertia morphism `forget X : I_X ⟶ X`
is finite, the algebraic space `Y` is locally Noetherian, and `p` is proper.
Let `f : X ⟶ M.toGroupoids` be a uniform categorical moduli space as
constructed in Theorem 106.13.9, and let `q : M ⟶ Y` be the induced morphism
with 2-cell `α : f ≫ AlgebraicSpace.toGroupoids.map q ≅ p`. Then `q` is
proper. -/
@[stacks 0DUZ] #check
  (AlgebraicGeometry.AlgebraicStack.proper_of_isUniformCategoricalModuliSpace :
    ∀
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y M : AlgebraicSpace S} [IsFinite (forget.{u + 1, u, u, u + 1} X)]
    [AlgebraicSpace.IsLocallyNoetherian Y] (p : X ⟶ Y.toGroupoids)
    [Proper p] (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpace f] (q : M ⟶ Y)
    (α : f ≫ AlgebraicSpace.toGroupoids.map q ≅ p),
    AlgebraicSpace.Proper q)

end AlgebraicGeometry.AlgebraicStack
