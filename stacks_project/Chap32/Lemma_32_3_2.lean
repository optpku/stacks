/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Surjective.Product
import StacksCheckRecall

universe u

/- Lemma 32.3.2: if each affine morphism `T i ⟶ S` is surjective, then the
product of the family in `CategoryTheory.Over S` is surjective over `S`. -/
@[stacks 0CNJ] #check
  (@AlgebraicGeometry.Scheme.Over.instSurjectivePiObjOfIsAffineHom :
    ∀ {I : Type u} (S : AlgebraicGeometry.Scheme.{u})
      (T : I → CategoryTheory.Over S)
      [∀ i, AlgebraicGeometry.IsAffineHom (T i).hom]
      [∀ i, AlgebraicGeometry.Surjective (T i).hom],
      AlgebraicGeometry.Surjective (CategoryTheory.Limits.piObj T).hom)
