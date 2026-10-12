/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.13.6: a quasi-compact immersion is a quasi-affine morphism. -/
@[stacks 02JR] #check
  (AlgebraicGeometry.IsImmersion.quasiAffineHom_of_quasiCompact :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S},
      IsImmersion f → QuasiCompact f → QuasiAffineHom f)
