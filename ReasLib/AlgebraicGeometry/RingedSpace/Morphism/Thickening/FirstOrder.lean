/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition

/-!
# First-order kernel comparison for morphisms of thickenings

The commutative square of a morphism of thickenings induces a map between the kernel
modules on the corresponding closed ringed spaces.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

/-- The first-order comparison map between the kernel modules of a morphism of thickenings. -/
noncomputable def sourceIdealMap {T U : Thickening.{u}}
    [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom] (g : T ⟶ U) :
    (g.left ^*).obj (RingedSpace.Hom.idealModule U.hom) ⟶
      RingedSpace.Hom.idealModule T.hom :=
  (RingedSpace.Hom.pullbackCompIso g.left U.hom).inv.app
      (RingedSpace.Hom.kernelIdealSheaf U.hom) ≫
    (eqToIso
        (congrArg (fun h : T.left ⟶ U.right ↦ RingedSpace.Hom.pullback h)
          (MorphismProperty.Arrow.w g))).hom.app
      (RingedSpace.Hom.kernelIdealSheaf U.hom) ≫
    (RingedSpace.Hom.pullbackCompIso T.hom g.right).hom.app
      (RingedSpace.Hom.kernelIdealSheaf U.hom) ≫
    (T.hom ^*).map (idealMap g)

/-- The first-order comparison map is the composite of pullback composition isomorphisms,
the square identification, and the induced map on kernel ideals. -/
theorem sourceIdealMap_spec {T U : Thickening.{u}}
    [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom] (g : T ⟶ U) :
    sourceIdealMap g =
      (RingedSpace.Hom.pullbackCompIso g.left U.hom).inv.app
          (RingedSpace.Hom.kernelIdealSheaf U.hom) ≫
        (eqToIso
            (congrArg (fun h : T.left ⟶ U.right ↦ RingedSpace.Hom.pullback h)
              (MorphismProperty.Arrow.w g))).hom.app
          (RingedSpace.Hom.kernelIdealSheaf U.hom) ≫
        (RingedSpace.Hom.pullbackCompIso T.hom g.right).hom.app
          (RingedSpace.Hom.kernelIdealSheaf U.hom) ≫
        (T.hom ^*).map (idealMap g) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
