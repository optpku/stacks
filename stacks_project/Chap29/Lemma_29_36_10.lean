/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth
import StacksCheckRecall

/-!
# Lemma 29.36.10

An etale morphism is syntomic.

@stack 02GQ
-/

@[expose] public section

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [Etale f]

/- Lemma 29.36.10: An étale morphism is syntomic. -/
@[stacks 02GQ] #check
  (AlgebraicGeometry.Smooth.syntomic (f := f) (inferInstance : Smooth f) : Syntomic f)
