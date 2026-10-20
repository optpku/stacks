/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FirstOrder
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

universe u

/- Situation 91.3.1 (1): a morphism of thickenings (f, f') is a commutative diagram
of ringed spaces whose horizontal arrows are thickenings. -/
@[stacks 08KZ] #check (AlgebraicGeometry.RingedSpace.Thickening.homMk :
  {T U : Thickening.{u}} → (f : T.left ⟶ U.left) → (f' : T.right ⟶ U.right) →
    f ≫ U.hom = T.hom ≫ f' → (T ⟶ U))

/- Situation 91.3.1 (2): set ℐ = ker T = Ker(i^♯) ⊂ 𝒪_{X'} and
𝒥 = ker U = Ker(t^♯) ⊂ 𝒪_{S'}. Then (f')^♯ induces the 𝒪_{X'}-module map
(f')^* 𝒥 ⟶ ℐ. -/
@[stacks 08KZ] #check (AlgebraicGeometry.RingedSpace.Thickening.Hom.idealMap :
  {T U : Thickening.{u}} → (g : T ⟶ U) →
    (Hom.pullback g.right).obj (Thickening.ker U).toModule ⟶ (Thickening.ker T).toModule)

/- Situation 91.3.1 (3), local erratum to the final assertion of 08KZ:
if i and t are first-order thickenings, the canonical comparison is
i^*((f')^* 𝒥) ≅ f^*(t^* 𝒥). The square-zero hypotheses identify t^* 𝒥 with 𝒥
and i^* ℐ with ℐ as closed-space modules. Applying i^* to the ambient ideal map
gives the 𝒪_X-module map f^* 𝒥 ⟶ ℐ checked below. The literal ambient equality
(f')^* 𝒥 = f^* 𝒥 does not hold in general. -/
@[stacks 08KZ] #check (AlgebraicGeometry.RingedSpace.Thickening.Hom.sourceIdealMap :
  {T U : Thickening.{u}} → [IsFirstOrderThickening T.hom] →
    [IsFirstOrderThickening U.hom] → (g : T ⟶ U) →
      (Hom.pullback g.left).obj (Hom.idealModule U.hom) ⟶ Hom.idealModule T.hom)
