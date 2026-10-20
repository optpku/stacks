module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt

/-! # Residue-field points induced by objects of groupoid fibrations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

open GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The field-valued point `Spec(κ(u0)) ⟶ X` induced by an object `x` over `U`
at a point `u0`. -/
def induced {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) : FieldValuedPoint X :=
  FieldValuedPoint.of (residueFieldType u0) (fromResidueField u0 ≫ hU)
    (overMap (Over.homMk (fromResidueField u0) rfl :
        Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU) ≫
      yonedaOfObject hU x hx)

/-- The induced field-valued point has source field `κ(u0)`, structure morphism
`fromResidueField u0 ≫ hU`, and 1-morphism obtained by precomposing
`yonedaOfObject` with `overMap`. -/
theorem induced_spec {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) :
    (induced hU x hx u0).K = residueFieldType u0 ∧
      (induced hU x hx u0).structureHom = fromResidueField u0 ≫ hU ∧
        (induced hU x hx u0).hom =
          overMap (Over.homMk (fromResidueField u0) rfl :
              Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU) ≫
            yonedaOfObject hU x hx := ⟨rfl, rfl, rfl⟩

/-- The residue-field point induced by a finite type point of a locally of
finite type scheme remains locally of finite type over the base. -/
instance instLocallyOfFiniteType_induced {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) [IsFiniteTypePoint u0] :
    AlgebraicGeometry.LocallyOfFiniteType (induced hU x hx u0).structureHom := by
  change AlgebraicGeometry.LocallyOfFiniteType (fromResidueField u0 ≫ hU)
  exact GroupoidsOver.instLocallyOfFiniteType_residuePoint hU u0


end AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
