module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-!
# Forgetting equivariance from quasi-coherent modules

This module defines the functor from equivariant quasi-coherent modules on a
groupoid scheme to quasi-coherent modules on its object scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

variable {S : Scheme.{u}}

/-- Forgetting equivariance preserves identity morphisms. -/
theorem forgetMap_id (G : GroupoidScheme S) (A : G.QCoh) :
    hom (𝟙 A) = 𝟙 A.obj :=
  rfl

/-- Forgetting equivariance preserves composition. -/
theorem forgetMap_comp (G : GroupoidScheme S) {A B C : G.QCoh}
    (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = hom f ≫ hom g :=
  rfl

/-- Forget equivariance from a groupoid-scheme quasi-coherent module. -/
def forget (G : GroupoidScheme S) : G.QCoh ⥤ Scheme.QCoh G.U.left where
  obj A := A.obj
  map f := hom f
  map_id := forgetMap_id G
  map_comp := forgetMap_comp G

/-- The forgetful functor returns the underlying quasi-coherent module. -/
theorem forget_obj (G : GroupoidScheme S) (A : G.QCoh) :
    (forget G).obj A = A.obj :=
  rfl

/-- The forgetful functor returns the underlying module morphism. -/
theorem forget_map (G : GroupoidScheme S) {A B : G.QCoh} (f : A ⟶ B) :
    (forget G).map f = hom f :=
  rfl

end AlgebraicGeometry.GroupoidScheme.QCoh
