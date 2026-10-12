/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
  [AlgebraicGeometry.IsFinite f]

/- Lemma 29.44.10: a finite morphism is quasi-finite. -/
@[stacks 02NU] #check (AlgebraicGeometry.Scheme.Hom.instQuasiFinite f :
  AlgebraicGeometry.Scheme.Hom.QuasiFinite f)
