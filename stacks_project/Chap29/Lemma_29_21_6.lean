/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Immersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.21.6: any open immersion is of finite presentation if and only if it is quasi-compact. -/
@[stacks 01TU] #check
  (AlgebraicGeometry.Scheme.Hom.finitePresentation_iff_quasiCompact_of_isOpenImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f],
      Scheme.Hom.FinitePresentation f ↔ QuasiCompact f)
