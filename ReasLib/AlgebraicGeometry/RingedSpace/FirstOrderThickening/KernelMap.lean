module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening

/-!
# Kernel comparisons for first-order thickenings

These maps compare kernel ideal modules across a commutative square of ringed-space
thickenings and record their adjunction descriptions.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S)

/-- The comparison of kernel ideal modules induced by a commutative square of first-order
thickenings. -/
def kernelMapOf {X' : RingedSpace.{u}} (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) (f' : X' ⟶ S') (w : i ≫ f' = f ≫ t) :
    RingedSpace.Hom.idealModule t ⟶ (f _*).obj (RingedSpace.Hom.idealModule i) :=
  (RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv
    (RingedSpace.Hom.idealModule t) (RingedSpace.Hom.idealModule i)
    (((RingedSpace.Hom.pullbackCompIso f t).symm ≪≫
        eqToIso (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pullback h) w.symm) ≪≫
        RingedSpace.Hom.pullbackCompIso i f').hom.app
      (RingedSpace.Hom.kernelIdealSheaf t) ≫
      (i^*).map
        (Hom.idealMap
          (homMk f f' w.symm : MorphismProperty.Arrow.mk i hi.toIsThickening ⟶ of t)))

/-- The inverse-image form of an `f`-map out of the kernel ideal module. -/
def cPull {G : X.Modules} (c : RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) :
    (f^*).obj (RingedSpace.Hom.idealModule t) ⟶ G :=
  (f^*).map c ≫ (RingedSpace.Hom.pullbackPushforwardAdjunction f).counit.app G

/-- The inverse-image adjunct of `kernelMapOf`. -/
theorem kernelMapOf_spec {X' : RingedSpace.{u}} (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) (f' : X' ⟶ S') (w : i ≫ f' = f ≫ t) :
    ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv
        (RingedSpace.Hom.idealModule t) (RingedSpace.Hom.idealModule i)).symm
      (kernelMapOf t f i hi f' w) =
      (((RingedSpace.Hom.pullbackCompIso f t).symm ≪≫
          eqToIso (congrArg (fun h : X ⟶ S' ↦ RingedSpace.Hom.pullback h) w.symm) ≪≫
          RingedSpace.Hom.pullbackCompIso i f').hom.app
        (RingedSpace.Hom.kernelIdealSheaf t) ≫
        (i^*).map
          (Hom.idealMap
            (homMk f f' w.symm : MorphismProperty.Arrow.mk i hi.toIsThickening ⟶ of t))) := sorry

/-- The adjunct of an `f`-map from the kernel ideal module. -/
theorem cPull_spec {G : X.Modules} (c : RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) :
    cPull t f c =
      ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv
        (RingedSpace.Hom.idealModule t) G).symm c := sorry

end AlgebraicGeometry.RingedSpace.Thickening
