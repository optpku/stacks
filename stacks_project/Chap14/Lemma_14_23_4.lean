/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Signed
import StacksCheckRecall

/-!
# Source-facing recall for Lemma 14.23.4

@stack 0198

The source-signed comparison from the lower-face normalized Moore complex to the alternating face
map complex is owned by ReasLib, both objectwise and as a natural transformation. Mathlib's
d₀-oriented comparison remains available as a convention-specific companion below.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology
open scoped Simplicial DoldKan

universe v u

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : SimplicialObject A)

/- Lemma 14.23.4: the source-signed lower-face normalized inclusions assemble into a chain map. -/
@[stacks 0198]
#check (normalizedMooreComplex.lowerFace.inclusion.app U :
  (normalizedMooreComplex.lowerFace.obj U) ⟶ (alternatingFaceMapComplex A).obj U)

/- The source-facing notation distinguishes the last-face convention from Mathlib's `N[U]`. -/
#check (Nₗ[U] : ChainComplex A ℕ)

variable (n : ℕ)

/- In every degree, this chain map is the canonical inclusion of the normalized Moore
subobject. -/
@[stacks 0198 "degreewise normalized Moore inclusion"]
#check (normalizedMooreComplex.lowerFace.inclusion.app_f U n :
  (normalizedMooreComplex.lowerFace.inclusion.app U).f n =
    (SimplicialObject.normalizedMoore.lowerFace.subobject U n).arrow)

@[stacks 0198 "natural source-signed normalized Moore inclusion"]
#check (normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A) :
  normalizedMooreComplex.lowerFace (A := A) ⟶ alternatingFaceMapComplex A)

/- Mathlib's d₀-oriented inclusion remains available as a convention-specific companion. -/
#check (inclusionOfMooreComplexMap U :
  (normalizedMooreComplex A).obj U ⟶ (alternatingFaceMapComplex A).obj U)
#check (inclusionOfMooreComplex A : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A)

end AlgebraicTopology
