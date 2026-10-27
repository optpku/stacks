/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.IsoClass

/-!
# The additive torsor of first-order solutions

Realization of every obstruction class makes the difference map bijective. Its inverse defines
the translation action and the based classification of compatible isomorphism classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Solution

variable {S S' X : RingedSpace.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S}
variable {G : X.Modules} {c : Hom.idealModule t ⟶ (f _*).obj G}

/-- Every obstruction class from an existing solution is realized by another solution. -/
theorem exists_solution_obstruction (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    ∃ sol : Solution t f G c, obstruction S0 sol = ξ := sorry

/-- Subtracting a fixed isomorphism class bijects the solution classes with the Ext¹ group. -/
theorem vsub_bijective (q : IsoClass t f G c) :
    Function.Bijective (fun p : IsoClass t f G c ↦ p -ᵥ q) := sorry

/-- Translation is the inverse of subtraction against the given isomorphism class. -/
def vadd (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (p : IsoClass t f G c) : IsoClass t f G c :=
  (Equiv.ofBijective (fun q : IsoClass t f G c ↦ q -ᵥ p) (vsub_bijective p)).symm ξ

/-- Ext¹ classes act on isomorphism classes of solutions by translation. -/
instance instVAdd_isoClass :
    VAdd (Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  vadd := vadd

/-- Translating by an Ext¹ class gives precisely that difference from the original class. -/
theorem vadd_spec (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (p : IsoClass t f G c) :
    (ξ +ᵥ p) -ᵥ p = ξ := sorry

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass t f G c) :
    (0 : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) +ᵥ p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd
    (ξ η : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
    (p : IsoClass t f G c) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p := sorry

/-- The Ext¹ translation action obeys the additive action laws. -/
instance instAddAction_isoClass :
    AddAction (Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (IsoClass t f G c) where
  add_vadd := add_vadd
  zero_vadd := vadd_zero

/-- Adding the difference to its second argument recovers its first argument. -/
theorem vsub_vadd (p q : IsoClass t f G c) : (p -ᵥ q) +ᵥ q = p := sorry

/-- Subtracting the base class from a translate recovers the translation parameter. -/
theorem vadd_vsub (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (p : IsoClass t f G c) :
    (ξ +ᵥ p) -ᵥ p = ξ := sorry

/-- With a chosen solution as basepoint, isomorphism classes are an additive torsor
under Ext⁽1⁾(Q NL[f], Q(𝒢[0])). -/
@[reducible]
def addTorsor (S0 : Solution t f G c) :
    AddTorsor (Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)))
      (IsoClass t f G c) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := vsub_vadd
  vadd_vsub' := vadd_vsub

/-- A basepoint solution makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : Solution t f G c) :
    Nonempty (IsoClass t f G c) := (addTorsor S0).nonempty

/-- A base solution identifies the Ext¹ group with all compatible solution classes. -/
def isoClassEquiv (S0 : Solution t f G c) :
    (Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) ≃ IsoClass t f G c :=
  (Equiv.ofBijective (fun p : IsoClass t f G c ↦ p -ᵥ isoClassMk S0)
    (vsub_bijective (isoClassMk S0))).symm

/-- The based chart sends an Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    isoClassEquiv S0 ξ = ξ +ᵥ isoClassMk S0 := sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : Solution t f G c) :
    isoClassEquiv S0 0 = isoClassMk S0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : Solution t f G c) (p : IsoClass t f G c) :
    (isoClassEquiv S0).symm p = p -ᵥ isoClassMk S0 := sorry

/-- A representative of the translated isomorphism class. -/
def translate (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (sol : Solution t f G c) : Solution t f G c :=
  Quotient.out (isoClassEquiv sol ξ)

/-- Translation of representatives agrees with the action on isomorphism classes. -/
theorem vadd_mk (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (sol : Solution t f G c) :
    ξ +ᵥ isoClassMk sol = isoClassMk (translate ξ sol) := sorry

/-- The representative translation realizes its prescribed obstruction. -/
theorem obstruction_translate (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) (sol : Solution t f G c) :
    obstruction sol (translate ξ sol) = ξ := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Solution
