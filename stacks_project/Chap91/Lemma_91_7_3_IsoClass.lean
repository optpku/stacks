/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import stacks_project.Chap91.Lemma_91_7_3_Translate

/-!
# Isomorphism classes of solutions of a first-order ringed-space equation

Two solutions of 91.7.0.1 are isomorphic when a fitting map exists for the
identity connecting cube. Their classes form a principal homogeneous space
under Ext⁽1⁾(Q NL[f], Q(𝒢[0])), via pushout translation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace CategoryTheory.Functor

/-- The functor on homotopy categories induced by the identity functor is canonically
isomorphic to the identity functor. -/
def mapHomotopyCategoryIdIso (A : Type u) [Category A] [Preadditive A] :
    (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived

/-- The homotopy-level identity-pullback model is canonically isomorphic to the
derived localization functor. -/
def idSourceIso (X : RingedSpace.{u}) :
    modulePullbackToDerived (𝟙 X) ≅
      (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) :=
  Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryIso (Hom.pullbackIdIso X)) ≪≫
        Functor.mapHomotopyCategoryIdIso X.Modules)
      (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) ≪≫
    Functor.leftUnitor _

/-- The canonical counit presenting the identity of `X.ModuleDerived` as a left-derived
model of pullback along `𝟙 X`. -/
def idCounit (X : RingedSpace.{u}) :
    (DerivedCategory.Qh : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
        X.ModuleDerived) ⋙
        Functor.id X.ModuleDerived ⟶ modulePullbackToDerived (𝟙 X) :=
  (Functor.rightUnitor _).hom ≫ (idSourceIso X).inv

/-- The identity functor with `idCounit` has the canonical left-derived universal property. -/
instance idFunctorIsLeftDerived (X : RingedSpace.{u}) :
    (Functor.id X.ModuleDerived).IsLeftDerivedFunctor
      (idCounit X) (RingedSpace.ModuleQis X) := sorry

/-- Derived pullback along the identity is canonically isomorphic to the identity functor. -/
def idIso (X : RingedSpace.{u}) :
    modulePullbackDerived (𝟙 X) ≅ Functor.id X.ModuleDerived :=
  Functor.leftDerivedNatIso
    (modulePullbackDerived (𝟙 X)) (Functor.id X.ModuleDerived)
    ((modulePullbackToDerived (𝟙 X)).totalLeftDerivedCounit
      DerivedCategory.Qh (RingedSpace.ModuleQis X))
    (idCounit X) (RingedSpace.ModuleQis X) (Iso.refl _)

/-- `idIso` identifies derived pullback along `𝟙 X` with the identity functor. -/
theorem idIso_hom_app (X : RingedSpace.{u}) (K : X.ModuleDerived) :
    (idIso X).hom.app K =
      (Functor.leftDerivedNatIso
        (modulePullbackDerived (𝟙 X)) (Functor.id X.ModuleDerived)
        ((modulePullbackToDerived (𝟙 X)).totalLeftDerivedCounit
          DerivedCategory.Qh (RingedSpace.ModuleQis X))
        (idCounit X) (RingedSpace.ModuleQis X) (Iso.refl _)).hom.app K := sorry

end AlgebraicGeometry.RingedSpace.modulePullbackDerived

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S S' X : RingedSpace.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S}
variable {G : X.Modules} {c : Hom.idealModule t ⟶ (f _*).obj G}

/-- A solution supplies a first-order thickening `i : X ⟶ X'`. -/
instance instIsFirstOrderThickening_sol (sol : Solution t f G c) :
    IsFirstOrderThickening sol.i :=
  sol.i_isFirstOrder

/-- The identity connecting cube comparing two solutions of the same equation, with
back face `S₁`, front face `S₂`, and `g = 𝟙 X`. -/
def compare (S₁ S₂ : Solution t f G c) :
    RelativeDiagram S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S') :=
  RelativeDiagram.of
    (CommDiagram.mk S₁.commutes S₂.commutes
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      ((Category.comp_id t).trans (Category.id_comp t).symm))
    (S₂.kernelIso.hom ≫ S₁.kernelIso.inv ≫
      (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S₁.i) ≫
      ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S₁.i)))
    sorry

/-- The identity connecting cube has identity maps on `X`, `S`, and `S'`, and `ν` is
the composite of the two kernel identifications. -/
theorem compare_spec (S₁ S₂ : Solution t f G c) :
    (compare S₁ S₂).comm.left.w = (Category.comp_id f).trans (Category.id_comp f).symm ∧
      (compare S₁ S₂).comm.bottom.w = (Category.comp_id t).trans (Category.id_comp t).symm := sorry

/-- The setoid identifying solutions that admit a fitting map of `compare`. -/
def isoSetoid (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) (G : X.Modules)
    (c : Hom.idealModule t ⟶ (f _*).obj G) :
    Setoid (Solution t f G c) where
  r S₁ S₂ := Nonempty (FittingMap (compare S₁ S₂))
  iseqv := sorry

/-- Two solutions are related iff the identity cube admits a fitting map. -/
theorem isoSetoid_rel (S₁ S₂ : Solution t f G c) :
    isoSetoid t f G c S₁ S₂ ↔ Nonempty (FittingMap (compare S₁ S₂)) := sorry

/-- Isomorphism classes of solutions of a fixed diagram 91.7.0.1. -/
abbrev IsoClass (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) (G : X.Modules)
    (c : Hom.idealModule t ⟶ (f _*).obj G) :=
  Quotient (isoSetoid t f G c)

/-- The isomorphism class of a given solution. -/
def isoClassMk (sol : Solution t f G c) : IsoClass t f G c :=
  Quotient.mk (isoSetoid t f G c) sol

/-- A fitting map of the identity cube identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {S₁ S₂ : Solution t f G c}
    (φ : FittingMap (compare S₁ S₂)) : isoClassMk S₁ = isoClassMk S₂ := sorry

/-- The obstruction class o(X'₁, X'₂) in Ext⁽1⁾(Q NL[f], Q(𝒢[0])), obtained by
transporting `mapObstruction` of the identity cube along L(𝟙 X)^* ≅ id and the
back kernel identification. -/
def obstruction (S₁ S₂ : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  (modulePullbackDerived.idIso X).inv.app ((moduleQ X).obj NL[f]) ≫
    mapObstruction (compare S₁ S₂) ≫
      (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
        ((moduleQ X).map
          ((CochainComplex.singleFunctor X.Modules 0).map S₁.kernelIso.hom))

/-- `obstruction` is `mapObstruction` of `compare`, transported to Ext⁽1⁾(Q NL[f], Q(𝒢[0])). -/
theorem obstruction_spec (S₁ S₂ : Solution t f G c) :
    obstruction S₁ S₂ =
      (modulePullbackDerived.idIso X).inv.app ((moduleQ X).obj NL[f]) ≫
        mapObstruction (compare S₁ S₂) ≫
          (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
            ((moduleQ X).map
              ((CochainComplex.singleFunctor X.Modules 0).map S₁.kernelIso.hom)) := sorry

/-- The obstruction vanishes if and only if the identity cube admits a fitting map. -/
theorem obstruction_eq_zero_iff (S₁ S₂ : Solution t f G c) :
    obstruction S₁ S₂ = 0 ↔ Nonempty (FittingMap (compare S₁ S₂)) := sorry

/-- Translating a solution by ξ realizes ξ as an obstruction. -/
theorem obstruction_translate
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (sol : Solution t f G c) :
    obstruction sol (translate ξ sol) = ξ := sorry

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
def vadd
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (p : IsoClass t f G c) : IsoClass t f G c :=
  Quotient.map (translate ξ) sorry p

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[X'_ξ] -ᵥ [X'] = ξ` when `o(X', X'_ξ) = ξ`. -/
def vsub (p q : IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  Quotient.lift₂ (fun S₁ S₂ ↦ obstruction S₂ S₁) sorry p q

/-- Ext¹ classes act on isomorphism classes of solutions by translation. -/
instance instVAdd_isoClass :
    VAdd (Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  vadd := vadd

/-- Difference of isomorphism classes of solutions is an Ext¹ class. -/
instance instVSub_isoClass :
    VSub (Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  vsub := vsub

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of solutions. -/
instance instAddAction_isoClass :
    AddAction (Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  add_vadd := sorry
  zero_vadd := sorry

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (sol : Solution t f G c) :
    ξ +ᵥ isoClassMk sol = isoClassMk (translate ξ sol) := sorry

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (S₁ S₂ : Solution t f G c) :
    isoClassMk S₁ -ᵥ isoClassMk S₂ = obstruction S₂ S₁ := sorry

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass t f G c) :
    (0 : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) +ᵥ p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd
    (ξ η : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (p : IsoClass t f G c) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p := sorry

/-- With a chosen solution as basepoint, isomorphism classes are an additive torsor
under Ext⁽1⁾(Q NL[f], Q(𝒢[0])). -/
@[reducible]
def addTorsor (S0 : Solution t f G c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- A basepoint solution makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : Solution t f G c) :
    Nonempty (IsoClass t f G c) := (addTorsor S0).nonempty

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
