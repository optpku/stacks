module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

universe u

/- 91.7.0.1: given a first-order thickening t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'}) with
𝒥 = Ker(t^♯), a morphism f : (X, 𝒪_X) ⟶ (S, 𝒪_S), an 𝒪_X-module 𝒢, and an
f-map c : 𝒥 ⟶ 𝒢, a solution of the displayed diagram
0 ⟶ 𝒢 ⟶ ? ⟶ 𝒪_X ⟶ 0 over 0 ⟶ 𝒥 ⟶ 𝒪_{S'} ⟶ 𝒪_S ⟶ 0
(vertical arrows f-maps) is a first-order thickening
i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'}) together with a morphism of thickenings (f, f')
whose kernel is identified with 𝒢 and such that (f')^♯ induces c. The unknown
middle ringed space X' is `Thickening.Solution.space`. -/
@[stacks 08U7] #check (AlgebraicGeometry.RingedSpace.Thickening.Solution :
  {S S' X : AlgebraicGeometry.RingedSpace.{u}} →
    (t : S ⟶ S') → [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t] →
    (f : X ⟶ S) → (G : X.Modules) →
    (AlgebraicGeometry.RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) → Type (u + 1))
