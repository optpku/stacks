/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_7_4_Class
import StacksCheckRecall

/-!
# Definition 72.7.4

The Weil divisor of a nonzero meromorphic section of an invertible module,
and the Weil divisor class of the module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 72.7.4 (1): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module.
For any nonzero meromorphic section `s` of `L` the Weil divisor associated to
`s` is `nonzeroMeromorphicSectionWeilDivisor s hs`, the locally finite sum
`∑ ord_{Z, L}(s) [Z]` in `Div(X)`, well-defined by Lemma 72.7.2. -/
@[stacks 0EPU] #check nonzeroMeromorphicSectionWeilDivisor

/- Definition 72.7.4 (2): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `L` be an invertible `𝒪_X`-module.
The Weil divisor class associated to `L` is the image of
`nonzeroMeromorphicSectionWeilDivisor s hs` in `Cl(X)` for any nonzero
meromorphic section `s` of `L`, well-defined by Lemma 72.7.3. -/
@[stacks 0EPU] #check invertibleModuleWeilDivisorClass
