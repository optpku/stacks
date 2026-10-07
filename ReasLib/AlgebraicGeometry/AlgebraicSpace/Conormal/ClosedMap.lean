module
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}
/-- Module pullback of algebraic spaces is a left adjoint, hence preserves
cokernels. -/
instance instIsLeftAdjoint_modulesPullback {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (Modules.pullback h).IsLeftAdjoint :=
  (Modules.pullbackPushforwardAdjunction h).isLeftAdjoint

namespace Hom.Conormal

/-- The pulled-back ideal of a closed immersion vanishes after mapping to
`i_* 𝒪_Z`. -/
theorem pulledIdeal_vanishes {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    IdealSubobject.pullbackMap (idealSheafSubobject i') g ≫ idealSheafMap i = 0 :=
  sorry

/-- The comparison `g^* I' ⟶ I` of kernel ideals of closed immersions in a
commutative square. -/
noncomputable def pulledIdealToIdeal {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback g).obj (idealSheaf i') ⟶ idealSheaf i :=
  kernel.lift (idealSheafMap i)
    (IdealSubobject.pullbackMap (idealSheafSubobject i') g)
    (pulledIdeal_vanishes sq) ≫
    (idealSheaf_spec i).inv

/-- The pulled ideal-sheaf action followed by `pulledIdealToIdeal ≫ π` is zero. -/
theorem pulledIdealAction_comp_π {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback g).map
          (Modules.idealAction (idealSheafSubobject i') (idealSheaf i')) ≫
        pulledIdealToIdeal sq ≫
          Modules.quotientByIdeal.π (idealSheafSubobject i) (idealSheaf i) =
      0 :=
  sorry

/-- For closed immersions, the source comparison `g^{-1}(I'/(I')²) ⟶ I/I²`. -/
noncomputable def idealQuotientMap {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    (Modules.pullback g).obj
        (Modules.quotientByIdeal (idealSheafSubobject i') (idealSheaf i')) ⟶
      Modules.quotientByIdeal (idealSheafSubobject i) (idealSheaf i) :=
  (PreservesCokernel.iso (Modules.pullback g)
      (Modules.idealAction (idealSheafSubobject i') (idealSheaf i'))).hom ≫
    cokernel.desc
      ((Modules.pullback g).map
        (Modules.idealAction (idealSheafSubobject i') (idealSheaf i')))
      (pulledIdealToIdeal sq ≫
        Modules.quotientByIdeal.π (idealSheafSubobject i) (idealSheaf i))
      (pulledIdealAction_comp_π sq)

/-- The closed-immersion comparison is cokernel descent of the pulled kernel
inclusion along the ideal-sheaf action. -/
theorem idealQuotientMap_eq {Z X Z' X' : AlgebraicSpace S}
    {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (sq : CommSq f i i' g) :
    idealQuotientMap sq =
      (PreservesCokernel.iso (Modules.pullback g)
          (Modules.idealAction (idealSheafSubobject i') (idealSheaf i'))).hom ≫
        cokernel.desc
          ((Modules.pullback g).map
            (Modules.idealAction (idealSheafSubobject i') (idealSheaf i')))
          (pulledIdealToIdeal sq ≫
            Modules.quotientByIdeal.π (idealSheafSubobject i) (idealSheaf i))
          (pulledIdealAction_comp_π sq) :=
  sorry


end Hom.Conormal
end AlgebraicGeometry.AlgebraicSpace
