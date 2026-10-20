module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension.Obstruction

open CategoryTheory
open AlgebraicGeometry (RingedSpace)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleExtension
open scoped AlgebraicGeometry

universe u

/- Lemma 91.4.2: For a first-order thickening of ringed spaces, endpoint maps between two
mixed-scalar module extensions with commuting infinitesimal-map square have an obstruction in
Ext¹ of the source cokernel by the target kernel. It vanishes exactly when a compatible middle
map exists. -/
@[stacks 08L6] #check (AlgebraicGeometry.RingedSpace.Hom.ModuleExtension.mapObstruction_eq_zero_iff :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    [HasExt.{u} X.Modules] (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ),
    mapObstruction E G φ ψ hcomm = 0 ↔
      ∃ φ' : E.middle ⟶ G.middle,
        E.ι ≫ φ' = (i _*).map ψ ≫ G.ι ∧
          φ' ≫ G.π = E.π ≫ (i _*).map φ)
