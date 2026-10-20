/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction

/-!
# Inverse-image ringed space (Y, g⁻¹ 𝒪_X)

The ringed space with underlying space Y and structure sheaf g⁻¹ 𝒪_X, together
with the canonical morphisms to X and from Y, restriction of coefficients along
g^♯, and the Ext¹ comparison of Lemma 17.31.3 with derived pullback.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {X Y : RingedSpace.{u}}

/-- The ringed space (Y, g⁻¹ 𝒪_X) obtained by pulling back the structure sheaf of
X along the underlying map of g. -/
def inverseImageSpace (g : Y ⟶ X) : RingedSpace.{u} :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).toRingedSpace

/-- The structure sheaf of `inverseImageSpace g` is g⁻¹ 𝒪_X. -/
theorem inverseImageSpace_sheaf (g : Y ⟶ X) :
    (inverseImageSpace g).sheaf =
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf := sorry

/-- The canonical morphism (Y, g⁻¹ 𝒪_X) ⟶ X with underlying map g and unit
structure map 𝒪_X ⟶ g_* g⁻¹ 𝒪_X. -/
def inverseImageTo (g : Y ⟶ X) : inverseImageSpace g ⟶ X :=
  InducedCategory.homMk
    { base := g.hom.base
      c :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            g.hom.base).unit.app X.sheaf).hom }

/-- The underlying continuous map of `inverseImageTo g` is the underlying map of g. -/
theorem inverseImageTo_base (g : Y ⟶ X) :
    (inverseImageTo g).hom.base = g.hom.base := sorry

/-- The morphism Y ⟶ (Y, g⁻¹ 𝒪_X) with identity underlying map and structure map
g^♯ : g⁻¹ 𝒪_X ⟶ 𝒪_Y. -/
def fromInverseImage (g : Y ⟶ X) : Y ⟶ inverseImageSpace g :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (inverseImageStructureSheafHomComm g).hom }

/-- The underlying continuous map of `fromInverseImage g` is the identity on Y. -/
theorem fromInverseImage_base (g : Y ⟶ X) :
    (fromInverseImage g).hom.base = 𝟙 Y.carrier := sorry

/-- The two canonical morphisms recover g. -/
theorem fromInverseImage_comp (g : Y ⟶ X) :
    fromInverseImage g ≫ inverseImageTo g = g := sorry

/-- Derived pullback along `g` is the composite `L(inverseImageTo g)^* ⋙ L(fromInverseImage g)^*`,
via `modulePullbackDerived.compIso` and `fromInverseImage_comp`. -/
def derivedPullbackCompIso_fromInverseImage (g : Y ⟶ X) :
    modulePullbackDerived (inverseImageTo g) ⋙
        modulePullbackDerived (fromInverseImage g) ≅
      modulePullbackDerived g :=
  (modulePullbackDerived.compIso (fromInverseImage g) (inverseImageTo g)
      (modulePullbackDerived.compComparison_isIso (fromInverseImage g)
        (inverseImageTo g))) ≪≫
    eqToIso
      (congrArg (fun h : Y ⟶ X ↦ modulePullbackDerived h) (fromInverseImage_comp g))

/-- The forward map of `derivedPullbackCompIso_fromInverseImage` is the composition comparison
followed by transport along `fromInverseImage_comp`. -/
theorem derivedPullbackCompIso_fromInverseImage_hom (g : Y ⟶ X) :
    (derivedPullbackCompIso_fromInverseImage g).hom =
      (modulePullbackDerived.compIso (fromInverseImage g) (inverseImageTo g)
          (modulePullbackDerived.compComparison_isIso (fromInverseImage g)
            (inverseImageTo g))).hom ≫
        (eqToIso
          (congrArg (fun h : Y ⟶ X ↦ modulePullbackDerived h)
            (fromInverseImage_comp g))).hom := sorry

/-- Restriction of scalars of an 𝒪_Y-module along g^♯, as a module on
(Y, g⁻¹ 𝒪_X). -/
def restrictToInverseImage (g : Y ⟶ X) (G : Y.Modules) :
    (inverseImageSpace g).Modules :=
  ((fromInverseImage g) _*).obj G

/-- `restrictToInverseImage` is pushforward of modules along `fromInverseImage`. -/
theorem restrictToInverseImage_spec (g : Y ⟶ X) (G : Y.Modules) :
    restrictToInverseImage g G = ((fromInverseImage g) _*).obj G := sorry

variable {S : RingedSpace.{u}}

/-- Lemma 17.31.3: the inverse image of `NL[f]` along `inverseImageTo g` is identified with
the naive cotangent complex of the inverse-image ring map. -/
def naiveCotangent_inverseImageIso (f : X ⟶ S) (g : Y ⟶ X) :
    TopCat.Sheaf.NaiveCotangent.InverseImage.source (inverseImageTo g).hom.base
        (inverseImageStructureSheafHomComm f) ≅
      TopCat.Sheaf.NaiveCotangent.InverseImage.target (inverseImageTo g).hom.base
        (inverseImageStructureSheafHomComm f) :=
  TopCat.Sheaf.NaiveCotangent.InverseImage.comparisonIso (inverseImageTo g).hom.base
    (inverseImageStructureSheafHomComm f)

/-- The forward map of `naiveCotangent_inverseImageIso` is the explicit inverse-image
comparison. -/
theorem naiveCotangent_inverseImageIso_hom (f : X ⟶ S) (g : Y ⟶ X) :
    (naiveCotangent_inverseImageIso f g).hom =
      TopCat.Sheaf.NaiveCotangent.InverseImage.comparison (inverseImageTo g).hom.base
        (inverseImageStructureSheafHomComm f) := sorry

/-- Underived comparison `(inverseImageTo g)^* NL[f] ⟶ NL[inverseImageTo g ≫ f]`. -/
def naiveCotangent_inverseImageTo (f : X ⟶ S) (g : Y ⟶ X) :
    ((inverseImageTo g)^*.mapHomologicalComplex (ComplexShape.up ℤ)).obj NL[f] ⟶
      NL[inverseImageTo g ≫ f] :=
  (NaiveCotangent.Pullback.chosenComplexIso (inverseImageTo g) f).hom ≫
    NaiveCotangent.left (inverseImageTo g) f

/-- `naiveCotangent_inverseImageTo` is the chosen pullback comparison followed by
transitivity. -/
theorem naiveCotangent_inverseImageTo_spec (f : X ⟶ S) (g : Y ⟶ X) :
    naiveCotangent_inverseImageTo f g =
      (NaiveCotangent.Pullback.chosenComplexIso (inverseImageTo g) f).hom ≫
        NaiveCotangent.left (inverseImageTo g) f := sorry

/-- Comparison `L(inverseImageTo g)^* Q NL[f] ⟶ Q NL[inverseImageTo g ≫ f]`. -/
def naiveCotangent_inverseImageToDerived (f : X ⟶ S) (g : Y ⟶ X) :
    (modulePullbackDerived (inverseImageTo g)).obj ((moduleQ X).obj NL[f]) ⟶
      (moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f] :=
  (Functor.LeftDerived.Homotopy.cochainCounit (inverseImageTo g)^*).app NL[f] ≫
    (moduleQ (inverseImageSpace g)).map (naiveCotangent_inverseImageTo f g)

/-- `naiveCotangent_inverseImageToDerived` is the cochain counit followed by
`naiveCotangent_inverseImageTo`. -/
theorem naiveCotangent_inverseImageToDerived_spec (f : X ⟶ S) (g : Y ⟶ X) :
    naiveCotangent_inverseImageToDerived f g =
      (Functor.LeftDerived.Homotopy.cochainCounit (inverseImageTo g)^*).app NL[f] ≫
        (moduleQ (inverseImageSpace g)).map (naiveCotangent_inverseImageTo f g) :=
  sorry

/-- Comparison `L(fromInverseImage)^* Q(G_restrict[0]) ⟶ Q(G[0])` from the
underived pullback-pushforward counit. -/
def extOne_inverseImageTgt (g : Y ⟶ X) (G : Y.Modules) :
    (modulePullbackDerived (fromInverseImage g)).obj
        ((moduleQ (inverseImageSpace g)).obj
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G))) ⟶
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G) :=
  (Functor.LeftDerived.Homotopy.cochainCounit (fromInverseImage g)^*).app
      ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
        (restrictToInverseImage g G)) ≫
    (moduleQ Y).map
      ((HomologicalComplex.singleMapHomologicalComplex (fromInverseImage g)^*
            (ComplexShape.up ℤ) (0 : ℤ)).hom.app
          (restrictToInverseImage g G) ≫
        (CochainComplex.singleFunctor Y.Modules 0).map
          ((pullbackPushforwardAdjunction (fromInverseImage g)).counit.app G))

/-- `extOne_inverseImageTgt` is the cochain counit followed by the adjunction
counit in degree zero. -/
theorem extOne_inverseImageTgt_spec (g : Y ⟶ X) (G : Y.Modules) :
    extOne_inverseImageTgt g G =
      (Functor.LeftDerived.Homotopy.cochainCounit (fromInverseImage g)^*).app
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G)) ≫
        (moduleQ Y).map
          ((HomologicalComplex.singleMapHomologicalComplex (fromInverseImage g)^*
                (ComplexShape.up ℤ) (0 : ℤ)).hom.app
              (restrictToInverseImage g G) ≫
            (CochainComplex.singleFunctor Y.Modules 0).map
              ((pullbackPushforwardAdjunction (fromInverseImage g)).counit.app G)) :=
  sorry

/-- Forward map of the displayed Ext¹ identification: pull back along
`fromInverseImage`, compare naive cotangents, then transport along
`derivedPullbackCompIso_fromInverseImage` into `Ext¹(L(g)^* NL[f], G)`. -/
def extOne_inverseImage (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f],
        (moduleQ (inverseImageSpace g)).obj
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G)))) :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  ShiftedHom.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((derivedPullbackCompIso_fromInverseImage g).inv.app ((moduleQ X).obj NL[f])))
    (ShiftedHom.comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((modulePullbackDerived (fromInverseImage g)).map
          (naiveCotangent_inverseImageToDerived f g)))
      (ShiftedHom.comp
        ((modulePullbackDerived (fromInverseImage g)).map ξ ≫
          ((modulePullbackDerived.commShift (fromInverseImage g)).commShiftIso
              (1 : ℤ)).hom.app
            ((moduleQ (inverseImageSpace g)).obj
              ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
                (restrictToInverseImage g G))))
        (ShiftedHom.mk₀ (0 : ℤ) rfl (extOne_inverseImageTgt g G))
        (zero_add (1 : ℤ)))
      (add_zero (1 : ℤ)))
    (add_zero (1 : ℤ))

/-- `naiveCotangent_inverseImageToDerived` is an isomorphism of derived objects. -/
instance instIsIso_naiveCotangent_inverseImageToDerived (f : X ⟶ S) (g : Y ⟶ X) :
    IsIso (naiveCotangent_inverseImageToDerived f g) := sorry

/-- Restriction of scalars along `fromInverseImage` preserves finite limits. -/
instance instPreservesFiniteLimits_fromInverseImage_pushforward (g : Y ⟶ X) :
    PreservesFiniteLimits ((fromInverseImage g)_*) := sorry

/-- Restriction of scalars along `fromInverseImage` preserves finite colimits. -/
instance instPreservesFiniteColimits_fromInverseImage_pushforward (g : Y ⟶ X) :
    PreservesFiniteColimits ((fromInverseImage g)_*) := sorry

/-- Cochain counit of pullback along `fromInverseImage` at `NL[inverseImageTo ≫ f]`. -/
def extOne_inverseImage_cochainCounit (f : X ⟶ S) (g : Y ⟶ X) :
    (modulePullbackDerived (fromInverseImage g)).obj
        ((moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f]) ⟶
      (moduleQ Y).obj
        ((((fromInverseImage g)^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          NL[inverseImageTo g ≫ f]) :=
  (Functor.LeftDerived.Homotopy.cochainCounit (fromInverseImage g)^*).app
    NL[inverseImageTo g ≫ f]

/-- The cochain counit of `fromInverseImage` at `NL[inverseImageTo ≫ f]` is an
isomorphism. -/
instance instIsIso_extOne_inverseImage_cochainCounit (f : X ⟶ S) (g : Y ⟶ X) :
    IsIso (extOne_inverseImage_cochainCounit f g) := sorry

/-- Derived unit `Q NL[inverseImageTo ≫ f] ⟶ (fromInverseImage)_* (L(g)^* Q NL[f])`,
via the underived adjunction unit, `mapDerivedCategoryFactors`, and transport along
the cochain counit, `naiveCotangent_inverseImageToDerived`, and
`derivedPullbackCompIso_fromInverseImage`. -/
def extOne_inverseImageUnitNL (f : X ⟶ S) (g : Y ⟶ X) :
    (moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f] ⟶
      ((fromInverseImage g)_*).mapDerivedCategory.obj
        ((modulePullbackDerived g).obj ((moduleQ X).obj NL[f])) :=
  (moduleQ (inverseImageSpace g)).map
      ((Adjunction.mapHomologicalComplexAdjunction
          (pullbackPushforwardAdjunction (fromInverseImage g))
          (ComplexShape.up ℤ)).unit.app NL[inverseImageTo g ≫ f]) ≫
    ((fromInverseImage g)_*).mapDerivedCategoryFactors.inv.app
      ((((fromInverseImage g)^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        NL[inverseImageTo g ≫ f]) ≫
    ((fromInverseImage g)_*).mapDerivedCategory.map
      ((asIso (extOne_inverseImage_cochainCounit f g)).inv ≫
        (modulePullbackDerived (fromInverseImage g)).map
            (asIso (naiveCotangent_inverseImageToDerived f g)).inv ≫
          (derivedPullbackCompIso_fromInverseImage g).hom.app
            ((moduleQ X).obj NL[f]))

/-- `extOne_inverseImageUnitNL` is the underived unit, `mapDerivedCategoryFactors`, and
transport along the cochain counit, `naiveCotangent_inverseImageToDerived`, and
`derivedPullbackCompIso_fromInverseImage`. -/
theorem extOne_inverseImageUnitNL_spec (f : X ⟶ S) (g : Y ⟶ X) :
    extOne_inverseImageUnitNL f g =
      (moduleQ (inverseImageSpace g)).map
          ((Adjunction.mapHomologicalComplexAdjunction
              (pullbackPushforwardAdjunction (fromInverseImage g))
              (ComplexShape.up ℤ)).unit.app NL[inverseImageTo g ≫ f]) ≫
        ((fromInverseImage g)_*).mapDerivedCategoryFactors.inv.app
          ((((fromInverseImage g)^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            NL[inverseImageTo g ≫ f]) ≫
        ((fromInverseImage g)_*).mapDerivedCategory.map
          ((asIso (extOne_inverseImage_cochainCounit f g)).inv ≫
            (modulePullbackDerived (fromInverseImage g)).map
                (asIso (naiveCotangent_inverseImageToDerived f g)).inv ≫
              (derivedPullbackCompIso_fromInverseImage g).hom.app
                ((moduleQ X).obj NL[f])) := sorry

/-- Degree `0` comparison
`(fromInverseImage)_* Q(G[0]) ⟶ Q((restrict G)[0])`, as `mapDerivedCategoryFactors`
followed by the single-complex comparison for restriction of scalars. -/
def extOne_inverseImageCoeffComparison (g : Y ⟶ X) (G : Y.Modules) :
    ((fromInverseImage g)_*).mapDerivedCategory.obj
        ((moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) ⟶
      (moduleQ (inverseImageSpace g)).obj
        ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
          (restrictToInverseImage g G)) :=
  ((fromInverseImage g)_*).mapDerivedCategoryFactors.hom.app
      ((CochainComplex.singleFunctor Y.Modules 0).obj G) ≫
    (moduleQ (inverseImageSpace g)).map
      ((HomologicalComplex.singleMapHomologicalComplex ((fromInverseImage g)_*)
            (ComplexShape.up ℤ) (0 : ℤ)).hom.app G)

/-- `extOne_inverseImageCoeffComparison` is `mapDerivedCategoryFactors` followed by
the single-complex comparison for restriction of scalars. -/
theorem extOne_inverseImageCoeffComparison_spec (g : Y ⟶ X) (G : Y.Modules) :
    extOne_inverseImageCoeffComparison g G =
      ((fromInverseImage g)_*).mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor Y.Modules 0).obj G) ≫
        (moduleQ (inverseImageSpace g)).map
          ((HomologicalComplex.singleMapHomologicalComplex ((fromInverseImage g)_*)
                (ComplexShape.up ℤ) (0 : ℤ)).hom.app G) := sorry

/-- Reverse tensor-hom map of the displayed Ext¹ identification: restriction of the
class along `(fromInverseImage)_*`, compared by `mapDerivedCategory`, then
precomposition with the derived unit. -/
def extOne_inverseImage_symm (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ζ :
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
        (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) :
    Ext⁽(1 : ℤ)⁾((moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f],
      (moduleQ (inverseImageSpace g)).obj
        ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
          (restrictToInverseImage g G))) :=
  ShiftedHom.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (extOne_inverseImageUnitNL f g))
    (ShiftedHom.comp
      (ζ.map ((fromInverseImage g)_*).mapDerivedCategory)
      (ShiftedHom.mk₀ (0 : ℤ) rfl (extOne_inverseImageCoeffComparison g G))
      (zero_add (1 : ℤ)))
    (add_zero (1 : ℤ))

/-- Tensor-hom adjunction and Lemma 17.31.3 identify
Ext¹_{g⁻¹ 𝒪_X}(NL_{g⁻¹ 𝒪_X / g⁻¹ f⁻¹ 𝒪_S}, G) with
Ext¹_{𝒪_Y}(L(g)^* NL[f], G). -/
def extOne_inverseImageIso (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules) :
    Ext⁽(1 : ℤ)⁾((moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f],
      (moduleQ (inverseImageSpace g)).obj
        ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
          (restrictToInverseImage g G))) ≃
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
        (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  Equiv.mk (extOne_inverseImage f g G) (extOne_inverseImage_symm f g G) sorry sorry

/-- The forward map of `extOne_inverseImageIso` is `extOne_inverseImage`. -/
theorem extOne_inverseImageIso_apply (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ (inverseImageSpace g)).obj NL[inverseImageTo g ≫ f],
        (moduleQ (inverseImageSpace g)).obj
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G)))) :
    extOne_inverseImageIso f g G ξ = extOne_inverseImage f g G ξ := sorry

/-- The reverse map of `extOne_inverseImageIso` is `extOne_inverseImage_symm`. -/
theorem extOne_inverseImageIso_symm_apply (f : X ⟶ S) (g : Y ⟶ X) (G : Y.Modules)
    (ζ :
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
        (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) :
    (extOne_inverseImageIso f g G).symm ζ = extOne_inverseImage_symm f g G ζ := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
