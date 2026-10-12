/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_7_2_Differentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Definition 76.7.2: Let S be a scheme. Let f : X ⟶ Y be a morphism of algebraic
spaces over S. The sheaf of differentials Ω_{X/Y} of X over Y is the sheaf of
differentials (Modules on Sites, Definition 18.33.10) for the morphism of ringed
topoi (f_small, f^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y) of Properties of Spaces,
Lemma 66.21.3. The universal Y-derivation will be denoted d_{X/Y} : 𝒪_X ⟶ Ω_{X/Y}. -/
@[stacks 04CT]
#check (Hom.relativeDifferentials f : X.Modules)

#check (Hom.universalDerivation f : Hom.derivations f (Hom.relativeDifferentials f))

#check (Ω[f] : X.Modules)

#check (d[f] : Hom.derivations f Ω[f])
