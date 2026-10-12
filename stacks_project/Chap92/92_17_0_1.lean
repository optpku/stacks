/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_17_0_1_Triangle»
import StacksCheckRecall

/- 92.17.0.1: for a ring map A → B and a B-module M, the functorial first
principal-parts sequence on C_{B/A} yields a distinguished triangle in D(B)
Algebra.CotangentComplex.Atiyah.tensorModule ⟶
Algebra.CotangentComplex.Atiyah.derivedPrincipalParts ⟶
M ⟶ (Algebra.CotangentComplex.Atiyah.tensorModule)⟦1⟧. -/
@[stacks 09DD]
#check Algebra.CotangentComplex.Atiyah.triangle_distinguished

#check Algebra.CotangentComplex.Atiyah.triangle
#check Algebra.CotangentComplex.Atiyah.tensorModule
#check Algebra.CotangentComplex.Atiyah.derivedPrincipalParts
#check Algebra.CotangentComplex.Atiyah.tensorToPrincipalParts
#check Algebra.CotangentComplex.Atiyah.principalPartsToModule
#check Algebra.CotangentComplex.Atiyah.connectingMap
