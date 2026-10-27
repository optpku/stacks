/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Fiber
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

universe u

/- Lemma 91.7.8 Let t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'}), 𝒥 = Ker(t^♯),
f : (X, 𝒪_X) ⟶ (S, 𝒪_S), 𝒢, and c : 𝒥 ⟶ 𝒢 be as in 91.7.0.1.
Denote ξ ∈ Ext¹_{𝒪_S}(NL_{S/S'}, 𝒥) the element corresponding to the
extension 𝒪_{S'} of 𝒪_S by 𝒥 via Lemma 91.7.4. The set of isomorphism classes
of solutions is canonically bijective to the fibre of
Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(L(f)^* NL_{S/S'}, 𝒢) over the image of ξ.
Here 𝒥 is `Hom.idealModule t`, ξ is `selfExtensionClass t`, the Ext¹ groups are
`Ext⁽1⁾(Q NL[f ≫ t], Q(𝒢[0]))` and `Ext⁽1⁾(L(f)^* NL[t], Q(𝒢[0]))`, the
displayed map is `extOne_comap t f`, the image of ξ is
`extOne_map (cPull t f c) (selfExtensionClass t)`, and the fibre is
`solutionExtFiber t f G c`. -/
@[stacks 0GQ3] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.isoClassFiberEquiv :
    ∀ {S S' X : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t]
      (f : X ⟶ S) (G : X.Modules) (c : Hom.idealModule t ⟶ (f _*).obj G),
      IsoClass t f G c ≃ solutionExtFiber t f G c)
