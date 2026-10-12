/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_12_1_Pullback
public import stacks_project.Chap78.Definition_78_12_1_System
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory
open GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/- Definition 78.12.1: For `B → S` as in Section 78.3 and a groupoid
`(U, R, s, t, c)` in algebraic spaces over `B`, a quasi-coherent module is a
pair `(F, α)` with `F` a quasi-coherent `𝒪_U`-module and
`α : t^* F ⟶ s^* F` an `𝒪_R`-module map such that the cocycle square on
`R ×_{s, U, t} R` commutes and `e^* α = 𝟙`. Compare with the commutative
diagrams of Lemma 78.11.4. -/
@[stacks 0441] #check (System G)

/- Companion: an equivariant quasi-coherent module is built from a quasi-coherent
module, an equivariance map, and the cocycle and unit laws. -/
#check System.of

/- Companion: `obj` and `action` recover the underlying module and the map
`t^* F ⟶ s^* F`. -/
#check System.obj
#check System.action

/- Companion: `spec` packages the cocycle and unit laws. -/
#check System.spec

/- Companion: `Cocycle` is the source square on `R ×_{s, U, t} R`, and `Unit`
is `e^* α = 𝟙`. -/
#check Cocycle
#check Unit
