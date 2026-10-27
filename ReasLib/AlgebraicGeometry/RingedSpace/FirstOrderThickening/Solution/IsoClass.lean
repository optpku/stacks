/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.MapObstruction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Assignment

/-!
# Compatible isomorphism classes of first-order solutions

The obstruction of the identity comparison cube descends to the quotient by compatible
isomorphisms. Reversing its arguments gives the difference of isomorphism classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Solution

variable {S S' X : RingedSpace.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S}
variable {G : X.Modules} {c : Hom.idealModule t ⟶ (f _*).obj G}

/-- The identity comparison of two solutions respects their prescribed kernel maps. -/
private theorem compare_kernelSquare (S₁ S₂ : Solution t f G c) :
    @KernelSquare _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance
      (@CommDiagram.mk _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance S₁.commutes S₂.commutes
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      ((Category.comp_id t).trans (Category.id_comp t).symm))
      (S₂.kernelIso.hom ≫ S₁.kernelIso.inv ≫
      (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S₁.i) ≫
      ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S₁.i))) := sorry

/-- The identity cube compares two solutions using their kernel identifications. -/
@[no_expose] def compare (S₁ S₂ : Solution t f G c) :
    @RelativeDiagram _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance :=
  @RelativeDiagram.of _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (@CommDiagram.mk _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance S₁.commutes S₂.commutes
      ((Category.comp_id f).trans (Category.id_comp f).symm)
      ((Category.comp_id t).trans (Category.id_comp t).symm))
    (S₂.kernelIso.hom ≫ S₁.kernelIso.inv ≫
      (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S₁.i) ≫
      ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S₁.i))) (compare_kernelSquare S₁ S₂)

/-- Compatible fillings of the identity comparison use the stored first-order certificates. -/
abbrev Fitting (S₁ S₂ : Solution t f G c) :=
  @FittingMap _ _ _ _ _ _ _ _
    S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
    S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂)

/-- A relative differential homomorphism perturbs a compatible filling between solutions. -/
def Fitting.perturb {S₁ S₂ : Solution t f G c} (φ : Fitting S₁ S₂)
    (α : Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S₁.i)) : Fitting S₁ S₂ :=
  @FittingMap.perturb _ _ _ _ _ _ _ _
    S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
    S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂) α φ

/-- The difference of two compatible fillings is a relative differential homomorphism. -/
def Fitting.diff {S₁ S₂ : Solution t f G c} (φ φ' : Fitting S₁ S₂) :
    Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S₁.i) :=
  @FittingMap.diff _ _ _ _ _ _ _ _
    S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
    S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂) φ φ'

/-- A compatible filling between two solutions of the same problem is an isomorphism. -/
theorem compare_fittingMap_isIso {S₁ S₂ : Solution t f G c}
    (φ : Fitting S₁ S₂) : IsIso (@FittingMap.hom _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance _ φ) := sorry

/-- The identity comparison has identity maps on the underlying deformation problem. -/
theorem compare_spec (S₁ S₂ : Solution t f G c) :
    (@CommDiagram.left _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance
      (@RelativeDiagram.comm _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂))).w = (Category.comp_id f).trans (Category.id_comp f).symm ∧
      (@CommDiagram.bottom _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance
      (@RelativeDiagram.comm _ _ _ _ _ _ _ _
      S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
      S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂))).w = (Category.comp_id t).trans (Category.id_comp t).symm := sorry

/-- Existence of a compatible filling is an equivalence relation on solutions. -/
private theorem isoRelation_equivalence :
    Equivalence (fun S₁ S₂ : Solution t f G c ↦ Nonempty (Fitting S₁ S₂)) := sorry

/-- The setoid identifying solutions that admit a fitting map of `compare`. -/
@[no_expose] def isoSetoid (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) (G : X.Modules)
    (c : Hom.idealModule t ⟶ (f _*).obj G) :
    Setoid (Solution t f G c) where
  r S₁ S₂ := Nonempty (Fitting S₁ S₂)
  iseqv := isoRelation_equivalence

/-- Two solutions are related iff the identity cube admits a fitting map. -/
theorem isoSetoid_rel (S₁ S₂ : Solution t f G c) :
    isoSetoid t f G c S₁ S₂ ↔ Nonempty (Fitting S₁ S₂) := sorry

/-- Isomorphism classes of solutions of a fixed first-order deformation problem. -/
abbrev IsoClass (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) (G : X.Modules)
    (c : Hom.idealModule t ⟶ (f _*).obj G) :=
  Quotient (isoSetoid t f G c)

/-- The isomorphism class of a given solution. -/
def isoClassMk (sol : Solution t f G c) : IsoClass t f G c :=
  Quotient.mk (isoSetoid t f G c) sol

/-- A fitting map of the identity cube identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {S₁ S₂ : Solution t f G c}
    (φ : Fitting S₁ S₂) : isoClassMk S₁ = isoClassMk S₂ := sorry

/-- The obstruction class o(X'₁, X'₂) in Ext⁽1⁾(Q NL[f], Q(𝒢[0])), obtained by
transporting `mapObstruction` of the identity cube along L(𝟙 X)^* ≅ id and the
back kernel identification. -/
def obstruction (S₁ S₂ : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  (modulePullbackDerived.idIso X).inv.app ((DerivedCategory.Q (C := X.Modules)).obj NL[f]) ≫
    @mapObstruction _ _ _ _ _ _ _ _
          S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
          S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂) ≫
      (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
        ((DerivedCategory.Q (C := X.Modules)).map
          ((CochainComplex.singleFunctor X.Modules 0).map S₁.kernelIso.hom))

/-- `obstruction` is `mapObstruction` of `compare`, transported to Ext⁽1⁾(Q NL[f], Q(𝒢[0])). -/
theorem obstruction_spec (S₁ S₂ : Solution t f G c) :
    obstruction S₁ S₂ =
      (modulePullbackDerived.idIso X).inv.app ((DerivedCategory.Q (C := X.Modules)).obj NL[f]) ≫
        @mapObstruction _ _ _ _ _ _ _ _
          S₁.i f S₁.f' t S₂.i f S₂.f' t (𝟙 X) (𝟙 S) (𝟙 S')
          S₁.i_isFirstOrder inferInstance S₂.i_isFirstOrder inferInstance (compare S₁ S₂) ≫
          (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map
            ((DerivedCategory.Q (C := X.Modules)).map
              ((CochainComplex.singleFunctor X.Modules 0).map S₁.kernelIso.hom)) := sorry

/-- The obstruction vanishes if and only if the identity cube admits a fitting map. -/
theorem obstruction_eq_zero_iff (S₁ S₂ : Solution t f G c) :
    obstruction S₁ S₂ = 0 ↔ Nonempty (Fitting S₁ S₂) := sorry

/-- The obstruction from a solution to itself vanishes. -/
theorem obstruction_self (sol : Solution t f G c) : obstruction sol sol = 0 := sorry

/-- Obstructions add under composition of comparisons. -/
theorem obstruction_add (A B C : Solution t f G c) :
    obstruction A C = obstruction A B + obstruction B C := sorry

/-- Obstruction is independent of the compatible representatives in both arguments. -/
private theorem obstruction_congr (A B A' B' : Solution t f G c)
    (hA : isoSetoid t f G c A A') (hB : isoSetoid t f G c B B') :
    obstruction B A = obstruction B' A' := sorry

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[X'_ξ] -ᵥ [X'] = ξ` when `o(X', X'_ξ) = ξ`. -/
@[no_expose] def vsub (p q : IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  Quotient.lift₂ (fun S₁ S₂ ↦ obstruction S₂ S₁) obstruction_congr p q

/-- Difference of isomorphism classes of solutions is an Ext¹ class. -/
instance instVSub_isoClass :
    VSub (Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  vsub := vsub

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (S₁ S₂ : Solution t f G c) :
    isoClassMk S₁ -ᵥ isoClassMk S₂ = obstruction S₂ S₁ := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Solution
