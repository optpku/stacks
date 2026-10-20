module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Basic
import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Computations.Object

/-!
# Cone computations for locally induced pseudopullback cones

This leaf exposes the ambient apex, legs, and comparison of a cone after locally induced
forgetting. It contains no action or universal-property statements.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA uB vB wB

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {A : Type uA} {B : Type uB} [Bicategory.{wB, vB} B]
variable {baseObj : A → B} {Q : Bicategory.HomProperty baseObj} [Q.IsMultiplicative]
variable {x y z : Bicategory.LocallyInducedBicategory B baseObj Q}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- The ambient apex of a forgotten locally induced pseudo-pullback cone. -/
@[simp]
theorem forgetLocallyInduced.pt (P : PseudoPullbackCone f g) :
    P.forgetLocallyInduced.pt = baseObj P.pt := sorry

/-- The ambient left leg of a forgotten locally induced pseudo-pullback cone. -/
@[simp]
theorem forgetLocallyInduced.fst (P : PseudoPullbackCone f g) :
    P.forgetLocallyInduced.fst = P.fst.obj := sorry

/-- The ambient right leg of a forgotten locally induced pseudo-pullback cone. -/
@[simp]
theorem forgetLocallyInduced.snd (P : PseudoPullbackCone f g) :
    P.forgetLocallyInduced.snd = P.snd.obj := sorry

/-- The ambient comparison of a forgotten locally induced pseudo-pullback cone. -/
@[simp]
theorem forgetLocallyInduced.iso (P : PseudoPullbackCone f g) :
    P.forgetLocallyInduced.iso =
      ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).mapFunctor P.pt z).mapIso P.iso := sorry

/-- The forward ambient comparison cell of a forgotten locally induced pseudo-pullback cone is
the ambient cell of the selected comparison. -/
@[simp]
theorem forgetLocallyInduced.iso.hom (P : PseudoPullbackCone f g) :
    P.forgetLocallyInduced.iso.hom = P.iso.hom.hom := sorry

/-- The inverse ambient comparison cell of a forgotten locally induced pseudo-pullback cone is
the ambient cell of the selected inverse comparison. -/
@[simp]
theorem forgetLocallyInduced.iso.inv (P : PseudoPullbackCone f g) :
    P.forgetLocallyInduced.iso.inv = P.iso.inv.hom := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
