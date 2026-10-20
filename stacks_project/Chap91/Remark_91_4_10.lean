module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Connecting
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening hiding Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

universe u

/- Remark 91.4.10. For a complex of first-order thickenings with compatible infinitesimal
maps and a short exact kernel sequence, the connecting map sends the canonical
extension class on the first thickening to the existence obstruction on the third. -/
@[stacks 08LF] #check
  (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.connecting_extClass_eq_existenceObstruction :
    ∀ {X X1 X2 X3 : RingedSpace.{u}}
      {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
      [IsFirstOrderThickening i1] [IsFirstOrderThickening i2] [IsFirstOrderThickening i3]
    (f : IsFirstOrderThickening.Hom i1 i2) (g : IsFirstOrderThickening.Hom i2 i3)
    (hC : IsComplex f g)
    [HasExt.{u} X.Modules]
    {F K1 K2 K3 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (c3 : kernelIdealSheaf i3 ⊗ (i3 _*).obj F ⟶ (i3 _*).obj K3)
    (κ32 : K3 ⟶ K2) (κ21 : K2 ⟶ K1) (w : κ32 ≫ κ21 = 0)
    (hκ : (ShortComplex.mk κ32 κ21 w).ShortExact)
    (hc12 : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ21)
    (hc23 : infinitesimalMapCommSqAlong g.hom g.w c2 c3 κ32)
    (E2 : InfinitesimalExtension i2 F K2 c2),
    (extClass_pushoutAlong f g hC c1 c2 κ21 hc12 E2).comp hκ.extClass (rfl : 1 + 1 = 2) =
      existenceObstruction i3 F K3 c3)
