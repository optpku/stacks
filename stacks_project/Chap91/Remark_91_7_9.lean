/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import stacks_project.Chap91.Lemma_91_7_8
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Ext² obstruction along a hypothetical Jacobi–Zariski triangle

In the 91.7.8 first-order ringed-space deformation setup, there are maps
L(f)* NL[t] ⟶ NL[f ≫ t] ⟶ NL[f]. They are close to a distinguished triangle
by Modules Lemma 17.31.7. If a connecting morphism γ completed them to a
distinguished triangle in D(𝒪_X), the connecting image of ξ in
Ext²(NL[f], 𝒢) would obstruct existence of a solution of 91.7.0.1.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

/- In the situation of Lemma 91.7.8 there are maps of complexes
L(f)* NL[t] ⟶ NL[f ≫ t] ⟶ NL[f]
(Stacks writes Lf* NL_{S'/S} for L(f)* NL_{S/S'} = L(f)* NL[t]).
These maps are close to a distinguished triangle, see Modules Lemma 17.31.7. -/
@[stacks 0GQ4] #check naiveCotangentComparison
@[stacks 0GQ4] #check AlgebraicGeometry.RingedSpace.NaiveCotangent.comparison
@[stacks 0GQ4] #check AlgebraicGeometry.RingedSpace.NaiveCotangent.transitivity

/-- The connecting Ext² class of an Ext¹ class along an explicit connecting morphism
γ : Q NL[f] ⟶ (L(f)* Q NL[t])⟦1⟧. -/
def connectingExtTwo
    (γ :
      (moduleQ X).obj NL[f] ⟶
        ((modulePullbackDerived f).obj ((moduleQ S).obj NL[t]))⟦(1 : ℤ)⟧)
    (ξ :
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived f).obj ((moduleQ S).obj NL[t]),
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    Ext⁽(2 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  ShiftedHom.comp γ ξ rfl

/-- `connectingExtTwo` is `ShiftedHom.comp` of `γ` with the Ext¹ class. -/
theorem connectingExtTwo_spec
    (γ :
      (moduleQ X).obj NL[f] ⟶
        ((modulePullbackDerived f).obj ((moduleQ S).obj NL[t]))⟦(1 : ℤ)⟧)
    (ξ :
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived f).obj ((moduleQ S).obj NL[t]),
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    connectingExtTwo t f G γ ξ = ShiftedHom.comp γ ξ rfl := sorry

/-- Remark 91.7.9 In the situation of Lemma 91.7.8 we have maps of complexes
L(f)* NL[t] ⟶ NL[f ≫ t] ⟶ NL[f]
(Stacks writes Lf* NL_{S'/S} for L(f)* NL_{S/S'} = L(f)* NL[t]).
These maps are close to forming a distinguished triangle, see Modules
Lemma 17.31.7. If a connecting morphism γ completed them to a distinguished
triangle in D(𝒪_X), then a solution of 91.7.0.1 exists if and only if the
connecting image of ξ in Ext²_{𝒪_X}(NL[f], 𝒢) vanishes. Here ξ is
`selfExtensionClass t`, its image in Ext¹(L(f)* NL[t], 𝒢) is
`extOne_map (cPull t f c) (selfExtensionClass t)`, and the Ext² class is
`connectingExtTwo`. -/
@[stacks 0GQ4]
theorem exists_iff_connecting_eq_zero
    (γ :
      (moduleQ X).obj NL[f] ⟶
        ((modulePullbackDerived f).obj ((moduleQ S).obj NL[t]))⟦(1 : ℤ)⟧)
    (hΔ :
      Triangle.mk (naiveCotangentComparison t f)
        ((moduleQ X).map (NaiveCotangent.comparison f t)) γ ∈
          distTriang (DerivedCategory X.Modules)) :
    Nonempty (IsoClass t f G c) ↔
      connectingExtTwo t f G γ
        (extOne_map (cPull t f c) (selfExtensionClass t)) = 0 := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
