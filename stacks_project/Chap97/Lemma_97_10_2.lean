/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Lemma_97_10_2_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

/- Lemma 97.10.2: for morphisms `Z ⟶ B`, `X ⟶ B`, and `B' ⟶ B` of algebraic spaces
over a scheme `S`, with `Z' = B' ×_B Z` and `X' = B' ×_B X`, the fppf sheaves on
`Sch/S` satisfy `Mor_{B'}(Z', X') ≅ B' ×_B Mor_B(Z, X)`. -/
@[stacks 05Y4]
#check (pullbackIso :
    ∀ {S : Scheme.{u}} {B B' : AlgebraicSpace S} (Z X : Over B) (h : B' ⟶ B),
      homSheaf (pullbackObj Z h) (pullbackObj X h) ≅
        pullback (uliftSheafMap h) (toBase Z X))
