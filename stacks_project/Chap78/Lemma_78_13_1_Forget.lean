/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_12_3_QCoh

/-!
# Forgetting equivariance from quasi-coherent modules

This module defines the functor from equivariant quasi-coherent modules on a
groupoid in algebraic spaces to quasi-coherent modules on its object space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Forgetting equivariance preserves identity morphisms. -/
theorem forgetMap_id (G : GroupoidAlgebraicSpace B) (A : G.QCoh) :
    hom (𝟙 A) = 𝟙 A.obj :=
  rfl

/-- Forgetting equivariance preserves composition. -/
theorem forgetMap_comp (G : GroupoidAlgebraicSpace B) {M N P : G.QCoh}
    (f : M ⟶ N) (g : N ⟶ P) :
    hom (f ≫ g) = hom f ≫ hom g :=
  rfl

/-- Forget equivariance from a groupoid-in-algebraic-spaces quasi-coherent module. -/
def forget (G : GroupoidAlgebraicSpace B) : G.QCoh ⥤ AlgebraicSpace.QCoh G.U.left where
  obj A := A.obj
  map f := hom f
  map_id := forgetMap_id G
  map_comp := forgetMap_comp G

/-- The forgetful functor returns the underlying quasi-coherent module. -/
theorem forget_obj (G : GroupoidAlgebraicSpace B) (A : G.QCoh) :
    (forget G).obj A = A.obj :=
  rfl

/-- The forgetful functor returns the underlying module morphism. -/
theorem forget_map (G : GroupoidAlgebraicSpace B) {M N : G.QCoh} (f : M ⟶ N) :
    (forget G).map f = hom f :=
  rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
