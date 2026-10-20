module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Étale lifting of geometric points of algebraic spaces

An étale morphism of algebraic spaces lifts a geometric point of the target to a
geometric point of the source with the same source field, lying over a prescribed
point of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- Reconstruct a geometric point of `U` from a morphism out of the source spectrum of `xbar`,
reusing the source field and structure morphism of `xbar`. -/
def ofHom {S : Scheme.{u}} {X U : AlgebraicSpace S} (xbar : GeometricPoint X)
    (h : ofOver xbar.overObj ⟶ U) : GeometricPoint U where
  K := xbar.K
  field := xbar.field
  structureHom := xbar.structureHom
  hom := h
  isAlgClosed := xbar.isAlgClosed

/-- The source field of `ofHom xbar h` is the source field of `xbar`. -/
@[simp]
theorem ofHom_K {S : Scheme.{u}} {X U : AlgebraicSpace S} (xbar : GeometricPoint X)
    (h : ofOver xbar.overObj ⟶ U) : (ofHom xbar h).K = xbar.K := sorry

/-- The structure morphism of `ofHom xbar h` is the structure morphism of `xbar`. -/
@[simp]
theorem ofHom_structureHom {S : Scheme.{u}} {X U : AlgebraicSpace S} (xbar : GeometricPoint X)
    (h : ofOver xbar.overObj ⟶ U) :
    (ofHom xbar h).structureHom = xbar.structureHom := sorry

/-- The morphism of `ofHom xbar h` is the supplied morphism. -/
@[simp]
theorem ofHom_hom {S : Scheme.{u}} {X U : AlgebraicSpace S} (xbar : GeometricPoint X)
    (h : ofOver xbar.overObj ⟶ U) : (ofHom xbar h).hom = h := sorry

/-- If `h` is a lift of `xbar` along `f`, then postcomposition recovers `xbar`. -/
theorem ofHom_map {S : Scheme.{u}} {X U : AlgebraicSpace S} (xbar : GeometricPoint X)
    (h : ofOver xbar.overObj ⟶ U) (f : U ⟶ X) (hf : h ≫ f = xbar.hom) :
    (ofHom xbar h).map f = xbar := sorry

/-- An étale morphism of algebraic spaces lifts a geometric point of the target to a morphism
from the same source spectrum, lying over a prescribed point of the source. -/
theorem exists_liftHom_of_etale {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x) (f : U ⟶ X) [Etale f]
    (u : Points U) (hu : Points.map f u = x) :
    ∃ h : ofOver xbar.overObj ⟶ U, h ≫ f = xbar.hom ∧ (ofHom xbar h).liesOver u := sorry

/-- An étale morphism of algebraic spaces lifts a geometric point of the target to a geometric
point of the source with the same source field, lying over a prescribed point of the source. -/
theorem exists_lift_of_etale {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x) (f : U ⟶ X) [Etale f]
    (u : Points U) (hu : Points.map f u = x) :
    ∃ ubar : GeometricPoint U, ubar.liesOver u ∧ ubar.map f = xbar := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
