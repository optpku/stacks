/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Definition 13.21.1 [015H]: a Cartan--Eilenberg resolution of a bounded-below cochain complex
is the neutral `CochainComplex.CartanEilenbergResolution` data owner.  Its row, column, cycles,
image, and horizontal-homology views are available in the same namespace. -/
@[stacks 015H]
#check @CochainComplex.CartanEilenbergResolution
