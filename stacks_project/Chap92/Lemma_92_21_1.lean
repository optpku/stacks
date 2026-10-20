/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Lemma_92_21_1_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Deformations of ringed spaces and the cotangent complex

In the first-order thickening situation of 92.21.0.1, solutions are governed by
Ext⁽n⁾_𝒪_X(L[f], G): a canonical class ξ in Ext⁽2⁾ vanishes iff a solution exists;
isomorphism classes of solutions are principal homogeneous under Ext⁽1⁾;
automorphisms of a given solution fitting the diagram are Ext⁽0⁾.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory
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

/-- Lemma 92.21.1 (1) In the situation above we have: there is a canonical element
ξ ∈ Ext⁽2⁾_𝒪_X(L[f], G) whose vanishing is a sufficient and necessary condition for the
existence of a solution to (92.21.0.1). -/
@[stacks 08UZ]
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction t f G c = 0 ↔ Nonempty (Solution t f G c) :=
  sorry

/-- Lemma 92.21.1 (2) If there exists a solution, then the set of isomorphism classes of
solutions is principal homogeneous under Ext⁽1⁾_𝒪_X(L[f], G). Existence is the basepoint S0;
the acting group is Ext⁽1⁾ of Q L[f] with coefficients Q(G[0]). -/
@[stacks 08UZ]
def isoClassDerivedEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾(derived f, coeffSingle G) ≃ IsoClass t f G c :=
  (extOneTruncEquiv f G).symm.trans (isoClassEquiv S0)

/-- The based chart sends a derived Ext¹ class to the translate of the basepoint. -/
theorem isoClassDerivedEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾(derived f, coeffSingle G)) :
    isoClassDerivedEquiv t f G c S0 ξ =
      isoClassEquiv S0 ((extOneTruncEquiv f G).symm ξ) :=
  sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassDerivedEquiv_zero (S0 : Solution t f G c) :
    isoClassDerivedEquiv t f G c S0 0 = isoClassMk S0 :=
  sorry

/-- The inverse chart is the naive torsor subtraction, transported along
`extOneTruncEquiv`. -/
theorem isoClassDerivedEquiv_symm_apply (S0 : Solution t f G c)
    (p : IsoClass t f G c) :
    (isoClassDerivedEquiv t f G c S0).symm p =
      extOneTruncEquiv f G ((isoClassEquiv S0).symm p) :=
  sorry

/-- Lemma 92.21.1 (3) Given a solution X', the set of automorphisms of X' fitting into
(92.21.0.1) is canonically isomorphic to Ext⁽0⁾_𝒪_X(L[f], G). The automorphism type is
FittingMap of the identity diagram compare S S. -/
@[stacks 08UZ]
def autEquiv (S : Solution t f G c) :
    Ext⁽(0 : ℤ)⁾(derived f, coeffSingle G) ≃ FittingMap (compare S S) where
  toFun e :=
    FittingMap.perturb (homToPerturb t f G c S ((extZeroHomEquiv f G).symm e)) (idFitting t f G c S)
  invFun φ :=
    extZeroHomEquiv f G (perturbToHom t f G c S (FittingMap.diff (idFitting t f G c S) φ))
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `autEquiv` sends an Ext⁰ class to the perturbation of `idFitting`. -/
theorem autEquiv_apply (S : Solution t f G c)
    (e : Ext⁽(0 : ℤ)⁾(derived f, coeffSingle G)) :
    autEquiv t f G c S e =
      FittingMap.perturb (homToPerturb t f G c S ((extZeroHomEquiv f G).symm e))
        (idFitting t f G c S) :=
  sorry

end AlgebraicGeometry.RingedSpace.Thickening
