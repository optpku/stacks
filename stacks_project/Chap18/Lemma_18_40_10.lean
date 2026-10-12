/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.10 (04IG): local morphisms of commutative ringed-site presentations are closed
under composition. -/
@[stacks 04IG]
#check @RingedSite.Hom.IsLocal.comp
