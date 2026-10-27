/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Obstruction
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
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

universe u

/- Remark 91.7.9 In the situation of Lemma 91.7.8 we have maps of complexes
L(f)* NL[t] ⟶ NL[f ≫ t] ⟶ NL[f]
(Stacks writes Lf* NL_{S'/S} for L(f)* NL_{S/S'} = L(f)* NL[t]).
These maps are close to forming a distinguished triangle, see Modules
Lemma 17.31.7. If a connecting morphism γ completed them to a distinguished
triangle in D(𝒪_X), then a solution of 91.7.0.1 exists if and only if the
connecting image of ξ in Ext²_{𝒪_X}(NL[f], 𝒢) vanishes. Here ξ is
`selfExtensionClass t`, its image in Ext¹(L(f)* NL[t], 𝒢) is
`extOne_map (cPull t f c) (selfExtensionClass t)`, and the Ext² class is
the degree-two composite `ShiftedHom.comp γ` with that image. -/
@[stacks 0GQ4] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.exists_iff_connecting_eq_zero :
    ∀ {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t]
      (f : X ⟶ S) (G : X.Modules) (c : Hom.idealModule t ⟶ (f _*).obj G)
      (gamma :
        (DerivedCategory.Q (C := X.Modules)).obj NL[f] ⟶
          ((modulePullbackDerived f).obj
            ((DerivedCategory.Q (C := S.Modules)).obj NL[t]))⟦(1 : ℤ)⟧)
      (hDelta :
        Triangle.mk (naiveCotangentComparison t f)
          ((DerivedCategory.Q (C := X.Modules)).map (NaiveCotangent.comparison f t)) gamma ∈
            distTriang (DerivedCategory X.Modules)),
      Nonempty (IsoClass t f G c) ↔
        ShiftedHom.comp gamma
          (extOne_map (cPull t f c) (selfExtensionClass t))
          (rfl : (1 : ℤ) + 1 = 2) = 0)

#check (AlgebraicGeometry.RingedSpace.NaiveCotangent.transitivity :
  ∀ {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    AlgebraicGeometry.RingedSpace.NaiveCotangent.Transitivity f g)
