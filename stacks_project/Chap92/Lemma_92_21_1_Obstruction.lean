module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Cochain
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
public import stacks_project.Chap91.Lemma_91_7_3
public import stacks_project.Chap91.Lemma_91_7_6_Map
public import stacks_project.Chap91.Lemma_91_7_8_Extension
public import stacks_project.Chap92.Lemma_92_20_2
public import stacks_project.Chap92.Lemma_92_20_3_Triangle
public import stacks_project.Chap92.Lemma_92_20_4

/-!
# Cotangent Ext² existence obstruction of a first-order thickening of ringed spaces

A first-order thickening t : S ⟶ S', a morphism f : X ⟶ S, an 𝒪_X-module G, and an
f-map c : Ker(t^♯) ⟶ f_* G determine a canonical class in Ext⁽2⁾(Q L[f], Q(G[0])).
The class is the connecting image of the tautological Ext¹ class of Lf^* NL[t] along
the transitivity triangle of f and t.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` and `distTriang` need that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

/-- The coefficient object `Q(G[0])` in `D(𝒪_X)`. -/
abbrev coeffSingle : DerivedCategory X.Modules :=
  (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)

/-- Unfolding of `coeffSingle` as the derived image of the degree-zero single complex. -/
theorem coeffSingle_eq :
    coeffSingle G =
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G) :=
  sorry

/-- The tautological Ext¹ class of `t` after derived pullback along `f` and the coefficient
map `c`. -/
def xiPrimeNaive :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived f).obj ((moduleQ S).obj NL[t]), coeffSingle G) :=
  extOne_map (cPull t f c) (selfExtensionClass t)

/-- `xiPrimeNaive` is `extOne_map` of `selfExtensionClass t` along `cPull t f c`. -/
theorem xiPrimeNaive_eq :
    xiPrimeNaive t f G c = extOne_map (cPull t f c) (selfExtensionClass t) :=
  sorry

/-- `xiPrimeNaive` is the 91.7.8 image of the tautological class of `t` along `c`. -/
theorem xiPrimeNaive_spec :
    xiPrimeNaive t f G c = extOne_postcomp (cPull t f c) (extOne_pullback f (selfExtensionClass t)) :=
  sorry

/-- Tower-level comparison `L(f⁻¹ t♯) ⟶ NL(f⁻¹ t♯)`. -/
def toNaiveTower :
    CotangentComplex.obj (NaiveCotangent.Tower.source f t)
        (Under.mk (NaiveCotangent.Tower.first f t)) ⟶
      SheafOfModules.RingedSite.NaiveCotangent.obj (NaiveCotangent.Tower.source f t)
        (Under.mk (NaiveCotangent.Tower.first f t)) :=
  CotangentComplex.toNaive (NaiveCotangent.Tower.source f t)
    (Under.mk (NaiveCotangent.Tower.first f t))

/-- Derived pullback of `NL[t]` agrees with underived pullback, so the cochain counit is an
isomorphism. -/
instance instIsIso_cochainCounit_naiveCotangent :
    IsIso ((Functor.LeftDerived.Homotopy.cochainCounit (f^*)).app NL[t]) :=
  sorry

/-- The cochain counit at `NL[t]`, as an isomorphism. -/
def cochainCounitNaiveIso :
    ((modulePullbackDerived f).obj ((moduleQ S).obj NL[t])) ≅
      ((moduleQ X).obj (((f^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj NL[t])) :=
  @asIso (DerivedCategory X.Modules) _ _ _
    ((Functor.LeftDerived.Homotopy.cochainCounit (f^*)).app NL[t])
    (instIsIso_cochainCounit_naiveCotangent t f)

/-- Comparison `Lf^* L[t] ⟶ Lf^* NL[t]` obtained from `toNaive` of the coefficient tower. -/
def toPullbackNaive :
    pullbackCotangent f t ⟶
      (modulePullbackDerived f).obj ((moduleQ S).obj NL[t]) :=
  DerivedCategory.Q.map
      (((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (toNaiveTower t f)) ≫
    DerivedCategory.Q.map (NaiveCotangent.Pullback.chosenComplexIso f t).inv ≫
    (cochainCounitNaiveIso t f).inv

/-- Unfolding of `toPullbackNaive` as the tower `toNaive`, `chosenComplexIso`, and the
derived-to-underived counit. -/
theorem toPullbackNaive_eq :
    toPullbackNaive t f =
      DerivedCategory.Q.map
          (((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map (toNaiveTower t f)) ≫
        DerivedCategory.Q.map (NaiveCotangent.Pullback.chosenComplexIso f t).inv ≫
        (cochainCounitNaiveIso t f).inv :=
  sorry

/-- The canonical Ext¹ class ξ' of `Lf^* L[t]` with coefficients `G`. -/
def xiPrime :
    Ext⁽(1 : ℤ)⁾(pullbackCotangent f t, coeffSingle G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
    (xiPrimeNaive t f G c) (add_zero (1 : ℤ))

/-- `xiPrime` is precomposition of `xiPrimeNaive` along `toPullbackNaive`. -/
theorem xiPrime_eq :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (xiPrimeNaive t f G c) (add_zero (1 : ℤ)) :=
  sorry

/-- `xiPrime` is the 91.7.8 image of the tautological class of `t` along `c`, transported
from `NL` to `L`. -/
theorem xiPrime_spec :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (extOne_map (cPull t f c) (selfExtensionClass t)) (add_zero (1 : ℤ)) :=
  sorry

/-- The canonical Ext² existence obstruction of the first-order deformation equation. -/
def existenceObstruction :
    Ext⁽(2 : ℤ)⁾(derived f, coeffSingle G) :=
  ShiftedHom.comp (connectingMap f t) (xiPrime t f G c) rfl

/-- `existenceObstruction` is `ShiftedHom.comp` of `connectingMap` with `xiPrime`. -/
theorem existenceObstruction_eq :
    existenceObstruction t f G c =
      ShiftedHom.comp (connectingMap f t) (xiPrime t f G c) rfl :=
  sorry

/-- `existenceObstruction` is the connecting image of the tautological class of `t` along `c`. -/
theorem existenceObstruction_spec :
    existenceObstruction t f G c =
      ShiftedHom.comp (connectingMap f t)
        (ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
          (xiPrimeNaive t f G c) (add_zero (1 : ℤ))) rfl :=
  sorry

/-- Derived morphism `L[f] ⟶ NL[f]` in `D(𝒪_X)`. -/
def toNaiveDerived : derived f ⟶ (moduleQ X).obj NL[f] :=
  (moduleQ X).map (toNaive f)

/-- Unfolding of `toNaiveDerived` as `Q.map` of `toNaive`. -/
theorem toNaiveDerived_eq :
    toNaiveDerived f = (moduleQ X).map (toNaive f) :=
  sorry

/-- Section `NL[f] ⟶ τ_{≥ -1} L[f]` in `D(𝒪_X)`, via `πTruncGE`, the truncation
quasi-isomorphism of `toNaive`, and the canonical `qHom` comparison. -/
def toTruncGESection :
    (moduleQ X).obj NL[f] ⟶ (DerivedCategory.TStructure.t.truncGE (-1)).obj (derived f) :=
  (moduleQ X).map ((naiveCotangent f).πTruncGE (-1)) ≫
    inv ((moduleQ X).map (CochainComplex.truncGEMap (toNaive f) (-1))) ≫
    inv (@DerivedCategory.TruncGE.qHom X.Modules _ _ _ (cotangentComplex f) (-1))

/-- Unfolding of `toTruncGESection`. -/
theorem toTruncGESection_eq :
    toTruncGESection f =
      (moduleQ X).map ((naiveCotangent f).πTruncGE (-1)) ≫
        inv ((moduleQ X).map (CochainComplex.truncGEMap (toNaive f) (-1))) ≫
        inv (@DerivedCategory.TruncGE.qHom X.Modules _ _ _ (cotangentComplex f) (-1)) :=
  sorry

/-- The shifted coefficient object `G[1]` lies in `t.GE (-1)`. -/
instance coeffSingle_shift_isGE :
    DerivedCategory.TStructure.t.IsGE ((coeffSingle G)⟦(1 : ℤ)⟧) (-1) :=
  DerivedCategory.TStructure.t.isGE_shift (coeffSingle G) (0 : ℤ) (1 : ℤ) (-1)

/-- The Ext¹ class of `NL[f]` obtained from a derived Ext¹ class by `descTruncGE`
and `toTruncGESection`. -/
def fromDerivedToNaiveExt (η : Ext⁽(1 : ℤ)⁾(derived f, coeffSingle G)) :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f], coeffSingle G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toTruncGESection f))
    (DerivedCategory.TStructure.t.descTruncGE (η : derived f ⟶ (coeffSingle G)⟦(1 : ℤ)⟧) (-1))
    (add_zero (1 : ℤ))

/-- The naive-to-derived Ext¹ comparison of `NL[f]` with `L[f]`. -/
def extOneTruncEquiv :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f], coeffSingle G) ≃
      Ext⁽(1 : ℤ)⁾(derived f, coeffSingle G) where
  toFun ξ :=
    ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived f)) ξ (add_zero (1 : ℤ))
  invFun η := fromDerivedToNaiveExt f G η
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extOneTruncEquiv` is precomposition along `toNaiveDerived`. -/
theorem extOneTruncEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f], coeffSingle G)) :
    extOneTruncEquiv f G ξ =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived f)) ξ
        (add_zero (1 : ℤ)) :=
  sorry

/-- The unshifted morphism `L[f] ⟶ G[0]` attached to a map out of `Ω[f]`. -/
def homKaehlerDerived (α : Ω[f] ⟶ G) : derived f ⟶ coeffSingle G :=
  (moduleQ X).map
    (CotangentComplex.augmentation (inverseImageStructureSheafHomComm f) ≫
      (CochainComplex.singleFunctor X.Modules 0).map α)

/-- The Hom representative of an Ext⁰ class, obtained from `H^0` along `homologyZeroIso`. -/
def homOfExtZero (e : Ext⁽(0 : ℤ)⁾(derived f, coeffSingle G)) : Ω[f] ⟶ G :=
  (homologyZeroIso f).inv ≫
    (DerivedCategory.homologyFunctorFactors X.Modules (0 : ℤ)).inv.app (cotangentComplex f) ≫
    (DerivedCategory.homologyFunctor X.Modules (0 : ℤ)).map
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm e) ≫
    (DerivedCategory.homologyFunctorFactors X.Modules (0 : ℤ)).hom.app
      ((CochainComplex.singleFunctor X.Modules 0).obj G) ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) G).hom

/-- The Ext⁰ identification `Hom(Ω[f], G) ≃ Ext⁽0⁾(Q L[f], Q(G[0]))`. -/
def extZeroHomEquiv : (Ω[f] ⟶ G) ≃ Ext⁽(0 : ℤ)⁾(derived f, coeffSingle G) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived f G α)
  invFun e := homOfExtZero f G e
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω[f] ⟶ G) :
    extZeroHomEquiv f G α = ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived f G α) :=
  sorry

/-- Transport a map `Ω[f] ⟶ G` to the perturb argument of the identity cube. -/
def homToPerturb (S : Solution t f G c) (α : Ω[f] ⟶ G) :
    Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S.i) :=
  α ≫ S.kernelIso.inv ≫
    (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S.i) ≫
    ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S.i))

/-- Unfolding of `homToPerturb` along `kernelIso` and the identity pullback unit. -/
theorem homToPerturb_eq (S : Solution t f G c) (α : Ω[f] ⟶ G) :
    homToPerturb t f G c S α =
      α ≫ S.kernelIso.inv ≫
        (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S.i) ≫
        ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S.i)) :=
  sorry

/-- Reverse transport from the perturb argument of the identity cube to `Ω[f] ⟶ G`. -/
def perturbToHom (S : Solution t f G c)
    (α : Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S.i)) : Ω[f] ⟶ G :=
  (pullbackIdIso X).inv.app Ω[f] ≫
    ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv Ω[f] (idealModule S.i)).symm α ≫
    S.kernelIso.hom

/-- Unfolding of `perturbToHom` along the identity pullback adjunction and `kernelIso`. -/
theorem perturbToHom_eq (S : Solution t f G c)
    (α : Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S.i)) :
    perturbToHom t f G c S α =
      (pullbackIdIso X).inv.app Ω[f] ≫
        ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv Ω[f] (idealModule S.i)).symm α ≫
        S.kernelIso.hom :=
  sorry

/-- The identity automorphism of a solution, as a fitting map of the identity diagram. -/
def idFitting (S : Solution t f G c) : FittingMap (compare S S) :=
  FittingMap.of (𝟙 S.space) sorry sorry sorry

/-- The underlying morphism of `idFitting` is the identity on the middle ringed space. -/
theorem idFitting_hom (S : Solution t f G c) :
    (idFitting t f G c S).hom = 𝟙 S.space :=
  sorry

end AlgebraicGeometry.RingedSpace.Thickening
