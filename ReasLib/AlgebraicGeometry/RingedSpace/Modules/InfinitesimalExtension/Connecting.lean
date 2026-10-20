module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.PushoutAlong
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Complex

/-!
# Connecting maps and existence obstructions for infinitesimal extensions

The canonical splitting of a complex of first-order thickenings identifies the
connecting image of a pushed-out extension class with its existence obstruction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening hiding Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X : RingedSpace.{u}}

variable {X1 X2 X3 : RingedSpace.{u}}
variable {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3]

/-- The canonical splitting of the first thickening in a complex of first-order thickenings,
packaged as the trivialization consumed by `extClass`. -/
noncomputable def canonicalSplit (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g) :
    Trivialization i1 :=
  Trivialization.ofRetraction (canonicalTrivialization f g hC)
    (canonicalTrivialization_leftInv f g hC)

/-- The underlying retraction of the canonical splitting is the canonical retraction
of the first thickening in the complex. -/
theorem canonicalSplit_retraction (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g) :
    (canonicalSplit f g hC).retraction = canonicalTrivialization f g hC :=
  rfl

/-- The degree-one extension class of the pushout, restricted along the canonical
splitting of the first thickening in a complex. -/
noncomputable def extClass_pushoutAlong (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g)
    [HasExt.{u} X.Modules]
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    Ext F K1 1 :=
  extClass (canonicalSplit f g hC) (pushoutAlong f c1 c2 κ hc E2)

/-- `extClass_pushoutAlong` is the `extClass` of the pushed-out extension along the
canonical splitting. -/
theorem extClass_pushoutAlong_eq (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g)
    [HasExt.{u} X.Modules]
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    extClass_pushoutAlong f g hC c1 c2 κ hc E2 =
      extClass (canonicalSplit f g hC) (pushoutAlong f c1 c2 κ hc E2) :=
  rfl

/-- For a complex of first-order thickenings and a short exact sequence of kernels
compatible with the infinitesimal maps, the connecting map sends the extension class
of the pushout on the canonically split first thickening to the existence obstruction
on the third thickening. The connecting map is Yoneda postcomposition with the class
of the kernel sequence. -/
@[stacks 08LF]
theorem connecting_extClass_eq_existenceObstruction
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
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    (extClass_pushoutAlong f g hC c1 c2 κ21 hc12 E2).comp hκ.extClass (rfl : 1 + 1 = 2) =
      existenceObstruction i3 F K3 c3 :=
  sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
