/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent
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
@[stacks 0441] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.System G : Type (u + 1))

/- Companion: an equivariant quasi-coherent module is built from a quasi-coherent
module, an equivariance map, and the cocycle and unit laws. -/
#check (System.of : (F : AlgebraicSpace.QCoh G.U.left) →
  (action : (AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj F) →
  Cocycle G F action → Unit G F action → System G)

/- Companion: `obj` and `action` recover the underlying module and the map
`t^* F ⟶ s^* F`. -/
#check (System.obj : System G → AlgebraicSpace.QCoh G.U.left)
#check (System.action : (A : System G) →
  (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj)

/- Companion: `spec` packages the cocycle and unit laws. -/
#check (System.spec : (A : System G) →
  Cocycle G A.obj A.action ∧ Unit G A.obj A.action)

/- Companion: `Cocycle` is the source square on `R ×_{s, U, t} R`, and `Unit`
is `e^* α = 𝟙`. -/
#check (Cocycle G : (F : AlgebraicSpace.QCoh G.U.left) →
  ((AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj F) → Prop)
#check (Unit G : (F : AlgebraicSpace.QCoh G.U.left) →
  ((AlgebraicSpace.QCoh.pullback G.t.left).obj F ⟶
    (AlgebraicSpace.QCoh.pullback G.s.left).obj F) → Prop)
