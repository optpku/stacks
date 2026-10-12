/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Relative
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relatively flat finitely presented quotients

This leaf owns the object properties selecting finitely presented, relatively flat quotient
modules on the two sides of a `FiberProductBaseChangeSituation`.

@stack 08KR
-/

open CategoryTheory

universe u

namespace FiberProductBaseChangeSituation

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- The property of a `D'`-module being finitely presented over `D'` and flat over `B'`. -/
@[stacks 08KR "finitely presented relative-flat modules"]
abbrev relativeFpFlatModuleProperty (S : Situation) : ObjectProperty (ModuleCat Dp) :=
  fun Q ↦ Module.FinitePresentation Dp Q ∧ RelativeFlat.moduleProperty S Q

/-- The property of a relative pullback object having finitely presented, relatively flat
components. -/
@[stacks 08KR "finitely presented relative-flat pullback objects"]
abbrev relativeFpFlatPullbackProperty
    (S : Situation) : ObjectProperty S.relativeModuleCategory :=
  fun Q ↦
    Module.FinitePresentation S.D Q.fst ∧
      Module.FinitePresentation S.CPrime Q.snd ∧ RelativeFlat.pullbackProperty S Q

/-- Remark 15.7.8 (1): surjective quotients of `L'` with finitely presented relatively flat
targets. -/
@[stacks 08KR "Remark 15.7.8 (1)"]
abbrev relativeFpFlatQuotientProperty
    (S : Situation) (L' : ModuleCat Dp) : ObjectProperty (Under L') :=
  fun Q ↦ Function.Surjective Q.hom.hom ∧ relativeFpFlatModuleProperty S Q.right

/-- Remark 15.7.8 (2): compatible componentwise surjective quotients of the relative base change
of `L'`, with finitely presented relatively flat targets. -/
@[stacks 08KR "Remark 15.7.8 (2)"]
abbrev relativeFpFlatPullbackQuotientProperty
    (S : Situation) (L' : ModuleCat Dp) :
    ObjectProperty (Under (S.relativeModuleFunctor.obj L')) :=
  fun Q ↦
    Function.Surjective Q.hom.fst.hom ∧
      Function.Surjective Q.hom.snd.hom ∧ relativeFpFlatPullbackProperty S Q.right

namespace RelativeFpFlatQuotient

/-- Relative module base change preserves the quotient conditions in Remark 15.7.8. -/
@[stacks 08KR "base change preserves finitely presented flat quotients"]
theorem baseChange_mem
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp)
    (Q : (relativeFpFlatQuotientProperty S L').FullSubcategory) :
    relativeFpFlatPullbackQuotientProperty S L'
      ((Under.post S.relativeModuleFunctor).obj Q.obj) := sorry

/-- The forward construction in Remark 15.7.8, obtained by applying relative module base change
to a quotient of `L'`. -/
@[stacks 08KR "forward base-change construction"]
noncomputable def baseChangeFunctor
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp) :
    (relativeFpFlatQuotientProperty S L').FullSubcategory ⥤
      (relativeFpFlatPullbackQuotientProperty S L').FullSubcategory :=
  (relativeFpFlatPullbackQuotientProperty S L').lift
    ((relativeFpFlatQuotientProperty S L').ι ⋙ Under.post S.relativeModuleFunctor)
    (baseChange_mem S hfp L')

/-- The canonical functor on under categories that sends a compatible quotient to its relative
fibre-product quotient. -/
@[stacks 08KR "relative fibre-product under functor"]
noncomputable def fiberProductUnderFunctor (S : Situation) (L' : ModuleCat Dp) :
    Under (S.relativeModuleFunctor.obj L') ⥤ Under L' :=
  Under.post (relativeRightAdjoint S) ⋙
    Under.map ((relativeAdjunction S).unit.app L')

/-- The relative fibre-product under functor restricted to compatible quotient objects, before
re-establishing the source quotient property. -/
@[stacks 08KR "relative fibre product on compatible quotients"]
noncomputable def fiberProductOnQuotients (S : Situation) (L' : ModuleCat Dp) :
    (relativeFpFlatPullbackQuotientProperty S L').FullSubcategory ⥤ Under L' :=
  (relativeFpFlatPullbackQuotientProperty S L').ι ⋙
    fiberProductUnderFunctor S L'

/-- The relative fibre-product right adjoint preserves the quotient conditions in
Remark 15.7.8. -/
@[stacks 08KR "fibre product preserves finitely presented flat quotients"]
theorem fiberProduct_mem
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp)
    (Q : (relativeFpFlatPullbackQuotientProperty S L').FullSubcategory) :
    relativeFpFlatQuotientProperty S L'
      ((fiberProductOnQuotients S L').obj Q) := sorry

/-- The inverse construction in Remark 15.7.8: take the relative fibre product of a compatible
pair of component quotients, with quotient map induced by the adjunction unit. -/
@[stacks 08KR "inverse fibre-product construction"]
noncomputable def fiberProductFunctor
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp) :
    (relativeFpFlatPullbackQuotientProperty S L').FullSubcategory ⥤
      (relativeFpFlatQuotientProperty S L').FullSubcategory :=
  (relativeFpFlatQuotientProperty S L').lift
    (fiberProductOnQuotients S L')
    (fiberProduct_mem S hfp L')

/-- The quotient map underlying `baseChangeFunctor` is the base change of the original quotient
map. -/
@[simp, stacks 08KR "forward quotient map"]
theorem baseChangeFunctor_obj_hom
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp)
    (Q : (relativeFpFlatQuotientProperty S L').FullSubcategory) :
    ((baseChangeFunctor S hfp L').obj Q).obj.hom =
      S.relativeModuleFunctor.map Q.obj.hom := sorry

/-- The quotient map underlying `fiberProductUnderFunctor` is the adjunction unit followed by the
map on relative fibre products. -/
@[simp, stacks 08KR "inverse quotient map"]
theorem fiberProductUnderFunctor_obj_hom
    (S : Situation) (L' : ModuleCat Dp)
    (Q : Under (S.relativeModuleFunctor.obj L')) :
    ((fiberProductUnderFunctor S L').obj Q).hom =
      (relativeAdjunction S).unit.app L' ≫
        (relativeRightAdjoint S).map Q.hom := sorry

/-- Remark 15.7.8: relative module base change gives an equivalence between relatively flat
finitely presented quotients and compatible componentwise quotients; the displayed
`fiberProductFunctor` is its canonical inverse construction. -/
@[stacks 08KR "Remark 15.7.8"]
theorem baseChange_isEquivalence
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp) :
    (baseChangeFunctor S hfp L').IsEquivalence := sorry

/-- The explicit fibre-product functor in Remark 15.7.8 is an equivalence. -/
@[stacks 08KR "fibre-product quotient equivalence"]
theorem fiberProduct_isEquivalence
    (S : Situation) (hfp : S.bprimeToDp.FinitePresentation) (L' : ModuleCat Dp) :
    (fiberProductFunctor S hfp L').IsEquivalence := sorry

end RelativeFpFlatQuotient

end FiberProductBaseChangeSituation

end
