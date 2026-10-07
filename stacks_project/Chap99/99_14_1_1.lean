module

public import stacks_project.Chap99.Lemma_99_14_2_Forget

/-!
# The forgetful functor from Polarized to Spaces'_{fp, flat, proper}
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p

noncomputable section

universe u

namespace AlgebraicGeometry

/-- 99.14.1.1: the forgetful functor Polarized ⟶ Spaces'_{fp, flat, proper} sends a
pair `(X ⟶ S, L)`, with `X ⟶ S` a proper flat finitely presented morphism of
schemes and `L` a relatively ample invertible `O_X`-module, to the underlying
family `(X ⟶ S)`. Morphisms `(f, g, φ)` are cartesian squares together with an
isomorphism `φ : f^* L ≅ L'`. Objects in the essential image have scheme total
spaces and bases. -/
@[stacks 0D3Y]
abbrev forgetToFpFlatProper := Polarized.toFpFlatProper

/-- The object map of `forgetToFpFlatProper` is `FpFlatProperGroupoids.mk (toHom x)`. -/
theorem forgetToFpFlatProper_obj (x : Polarized.Obj) :
    forgetToFpFlatProper.obj x = FpFlatProperGroupoids.mk (Polarized.toHom x) :=
  sorry

/-- The morphism map of `forgetToFpFlatProper` forgets the line-bundle isomorphism. -/
theorem forgetToFpFlatProper_map {x y : Polarized.Obj} (φ : x ⟶ y) :
    forgetToFpFlatProper.map φ = Polarized.toFpFlatProperHom φ :=
  sorry

end AlgebraicGeometry
