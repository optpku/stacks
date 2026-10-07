module

public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Remark_67_12_4_Coborder
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- Definition 76.5.1: Let `i : Z ⟶ X` be an immersion of algebraic spaces. The
conormal sheaf `C_{Z/X}` of `Z` in `X`, or the conormal sheaf of `i`, is the
quasi-coherent `𝒪_Z`-module `I / I²` of the coborder closed immersion
`Z ⟶ X \ ∂Z`. -/
@[stacks 04CN]
#check
  ((Modules.pullback (IsImmersion.liftCoborder i)).obj
      (Modules.quotientByIdeal
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i))) :
    Z.Modules)
