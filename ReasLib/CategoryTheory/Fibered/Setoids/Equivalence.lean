module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Equivalence
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses

/-!
# Equivalence criteria for categories fibred in setoids

This module collects the consequences of equivalences over a fixed base for
the setoid-fibred condition and for fiberwise isomorphism classes.
-/

@[expose] public section

universe u v uS vS uX vX uY vY

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

namespace IsEquivalence

/-- Equivalence over a fixed base transports the fibred-in-setoids property from its target to
its source, with independent universes for both total categories. -/
theorem sourceInSetoids
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsFibered.InSetoids Y.p] :
    Functor.IsFibered.InSetoids X.p := sorry
/- Proof strategy: use the chosen quasi-inverse to transport fibredness and the induced equivalence
on each standard fiber to transport groupoidality and thinness. -/

/-- Equivalence over a fixed base transports the fibred-in-setoids property from its source to its
target. This is the symmetric companion of `sourceInSetoids`. -/
theorem targetInSetoids
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsFibered.InSetoids X.p] :
    Functor.IsFibered.InSetoids Y.p := sorry

end IsEquivalence

/-- A category over `C` which is equivalent over `C` to a category fibred in sets is fibred in
setoids. -/
@[stacks 0045 "equivalence to a discrete fibration gives setoid fibers"]
theorem IsEquivalence.sourceInSetoids.of_targetSets
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsDiscreteFibration Y.p] :
    Functor.IsFibered.InSetoids X.p := sorry
/- Proof strategy: regard the target as fibred in setoids and apply
`BasedFunctor.IsEquivalence.sourceInSetoids`. -/

/-- For an equivalence over `C` whose target is fibred in sets, the canonical map from
isomorphism classes in each source fiber to target-fiber objects is bijective. -/
@[stacks 0045 "fiberwise isomorphism classes are bijective"]
theorem IsEquivalence.fiberIsoClasses.bijective
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsDiscreteFibration Y.p] (U : C) :
    Function.Bijective (F.fiberFunctor U).isoClassesToObj := sorry
/- Proof strategy: `F.fiberFunctor.isEquivalence` and discreteness of the target fiber reduce this
to `Functor.isoClassesToObj.bijective_of_isEquivalence`. -/

/-- An equivalence over the base identifies source-fiber isomorphism classes with objects of a
discrete target fiber.

Its forward map is the canonical `isoClassesToObj`, as in the neutral
`Functor.IsEquivalence.isoClassesEquiv`. The inverse is deliberately the class of the image
under the named based quasi-inverse `F.inv`, retaining the stronger fiberwise computation rule
rather than exposing the unrelated categorical choice made for the induced fiber functor. -/
@[stacks 0045 "fiberwise class equivalence"]
noncomputable def IsEquivalence.fiberIsoClasses.equiv
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsDiscreteFibration Y.p] (U : C) :
    isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U where
  toFun := (F.fiberFunctor U).isoClassesToObj
  invFun := fun y => Quotient.mk'' ((F.inv.fiberFunctor U).obj y)
  left_inv := sorry
  right_inv := sorry
/- Axiom audit: both functions are explicit. `toFun` is the canonical quotient map and `invFun`
uses the named inverse based functor; `sorryAx` occurs only in the two Prop-valued inverse laws. -/

/-- The forward map of `BasedFunctor.IsEquivalence.fiberIsoClasses.equiv` sends a represented class to
the image of its representative under the fiber functor. -/
@[simp]
theorem IsEquivalence.fiberIsoClasses.equiv.apply
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsDiscreteFibration Y.p]
    (U : C) (x : X.p.Fiber U) :
    IsEquivalence.fiberIsoClasses.equiv F U (Quotient.mk'' x) =
      (F.fiberFunctor U).obj x := sorry
/- Proof strategy: apply `Functor.isoClassesToObj.mk` to `F.fiberFunctor U`. -/

/-- The inverse map of `BasedFunctor.IsEquivalence.fiberIsoClasses.equiv` takes the class of the image
under the named inverse fiber functor. -/
@[simp]
theorem IsEquivalence.fiberIsoClasses.equiv.symm_apply
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [Functor.IsDiscreteFibration Y.p]
    (U : C) (y : Y.p.Fiber U) :
    (IsEquivalence.fiberIsoClasses.equiv F U).symm y =
      Quotient.mk'' ((F.inv.fiberFunctor U).obj y) := sorry
/- Proof strategy: unfold the inverse function of the explicit equivalence. -/

namespace QuasiInverse

variable {F : X ⥤ᵇ Y}

/-- Explicit quasi-inverse data identify source-fibre isomorphism classes with objects of a
discrete target fibre. Both functions are determined by `F` and the supplied `e.inverse`; no
property-level inverse is selected. -/
@[stacks 0045 "explicit fibrewise class equivalence"]
noncomputable def fiberIsoClasses.equiv
    (e : QuasiInverse F) [Functor.IsDiscreteFibration Y.p] (U : C) :
    isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U where
  toFun := (F.fiberFunctor U).isoClassesToObj
  invFun := fun y ↦ Quotient.mk'' ((e.inverse.fiberFunctor U).obj y)
  left_inv := sorry
  right_inv := sorry

/-- The explicit fibre-class equivalence applies the forward fibre functor to a represented
class. -/
@[simp]
theorem fiberIsoClasses.equiv.apply
    (e : QuasiInverse F) [Functor.IsDiscreteFibration Y.p]
    (U : C) (x : X.p.Fiber U) :
    fiberIsoClasses.equiv e U (Quotient.mk'' x) =
      (F.fiberFunctor U).obj x := sorry

/-- The inverse of the explicit fibre-class equivalence applies the supplied inverse fibre
functor and takes its isomorphism class. -/
@[simp]
theorem fiberIsoClasses.equiv.symm_apply
    (e : QuasiInverse F) [Functor.IsDiscreteFibration Y.p]
    (U : C) (y : Y.p.Fiber U) :
    (fiberIsoClasses.equiv e U).symm y =
      Quotient.mk'' ((e.inverse.fiberFunctor U).obj y) := sorry

end QuasiInverse

end BasedFunctor

namespace BasedCategory

variable {X Y : BasedCategory.{vS, uS} C}

/-- If `X` is equivalent to `Y` in `BasedCategory C` and `Y.p` is a discrete fibration, then
`X.p` is fibred in setoids. -/
@[stacks 0045 "based equivalence to a discrete fibration"]
theorem Equivalence.inSetoids.of_targetDiscrete
    (e : X ≌ Y) [Functor.IsDiscreteFibration Y.p] :
    Functor.IsFibered.InSetoids X.p := sorry
/- Proof strategy: use closure of the fibred-in-setoids object property under bicategorical
equivalence and the canonical implication from discrete fibrations to setoid fibrations. -/

/-- For an equivalence in `BasedCategory C` whose target is a discrete fibration, the induced map
from source-fiber isomorphism classes to target-fiber objects is bijective. -/
@[stacks 0045 "based fiberwise isomorphism classes are bijective"]
theorem Equivalence.fiberIsoClasses.bijective
    (e : X ≌ Y) [Functor.IsDiscreteFibration Y.p] (U : C) :
    Function.Bijective (e.hom.fiberFunctor U).isoClassesToObj := sorry
/- Proof strategy: restrict `e` to the fiber over `U`; essential surjectivity gives surjectivity
onto the discrete target fiber, while full faithfulness and discreteness give injectivity on
source isomorphism classes. -/

/-- A fixed bicategorical equivalence identifies source-fiber isomorphism classes with objects of
each discrete target fiber. Unlike the heterogeneous property-level version, its inverse function
is directly the class of the image under the supplied `e.inv`. It is the fiberwise counterpart of
`Equivalence.isoClassesEquiv`, with an inverse that computes through the supplied bicategorical
inverse. -/
@[stacks 0045 "based fiberwise class equivalence"]
def Equivalence.fiberIsoClasses.equiv
    (e : X ≌ Y) [Functor.IsDiscreteFibration Y.p] (U : C) :
    isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U where
  toFun := (e.hom.fiberFunctor U).isoClassesToObj
  invFun := fun y => Quotient.mk'' ((e.inv.fiberFunctor U).obj y)
  left_inv := sorry
  right_inv := sorry
/- Axiom audit: the forward and inverse functions are explicit functions of `e.hom` and `e.inv`.
Only the Prop-valued inverse laws remain deferred. -/

/-- The forward map of `BasedCategory.Equivalence.fiberIsoClasses.equiv` is the ordinary induced fiber
functor on a represented isomorphism class. -/
@[simp]
theorem Equivalence.fiberIsoClasses.equiv.apply
    (e : X ≌ Y) [Functor.IsDiscreteFibration Y.p]
    (U : C) (x : X.p.Fiber U) :
    Equivalence.fiberIsoClasses.equiv e U (Quotient.mk'' x) =
      (e.hom.fiberFunctor U).obj x := sorry
/- Proof strategy: apply `Functor.isoClassesToObj.mk` to `e.hom.fiberFunctor U`. -/

/-- The inverse map of `BasedCategory.Equivalence.fiberIsoClasses.equiv` takes the class of the image
under the supplied inverse fiber functor. -/
@[simp]
theorem Equivalence.fiberIsoClasses.equiv.symm_apply
    (e : X ≌ Y) [Functor.IsDiscreteFibration Y.p]
    (U : C) (y : Y.p.Fiber U) :
    (Equivalence.fiberIsoClasses.equiv e U).symm y =
      Quotient.mk'' ((e.inv.fiberFunctor U).obj y) := sorry
/- Proof strategy: unfold the inverse function of the explicit equivalence. -/

end BasedCategory

end CategoryTheory
