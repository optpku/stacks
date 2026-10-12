/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.PullbackSolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- 92.21.0.1: given a first-order thickening t : (S, 𝒪_S) ⟶ (S', 𝒪_S') with
𝒥 = Ker(t♯), a morphism f : (X, 𝒪_X) ⟶ (S, 𝒪_S), an 𝒪_X-module 𝒢, and an f-map
c : 𝒥 ⟶ 𝒢, a solution of the diagram
0 ⟶ 𝒢 ⟶ 𝒪_X' ⟶ 𝒪_X ⟶ 0 over 0 ⟶ 𝒥 ⟶ 𝒪_S' ⟶ 𝒪_S ⟶ 0
is a first-order thickening i : (X, 𝒪_X) ⟶ (X', 𝒪_X') together with a morphism of
thickenings (f, f') such that Ker(i♯) is identified with 𝒢 and (f')♯ induces c. -/
@[stacks 08UY] #check (AlgebraicGeometry.RingedSpace.Thickening.PullbackSolution :
  ∀ {S S' X : AlgebraicGeometry.RingedSpace.{u}} (t : S ⟶ S')
    [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t] (f : X ⟶ S) {G : X.Modules}
    (c : (f^*).obj (AlgebraicGeometry.RingedSpace.Hom.idealModule t) ⟶ G), Type (u + 1))
#check AlgebraicGeometry.RingedSpace.Thickening.PullbackSolution.of
#check AlgebraicGeometry.RingedSpace.Thickening.PullbackSolution.spec
