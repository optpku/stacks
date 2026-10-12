/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_10_5_Comparison

/-!
# Lemma 71.10.5

If an algebraic space `X` over `S` is representable by a scheme `T.left`, every weakly
associated point of `X` has codimension `0`, and `X` satisfies Morphisms of Spaces
Lemma 67.49.1, then the étale sheaf of meromorphic functions `𝒦_X` is the quasi-coherent
`𝒪_X`-algebra associated to the Zariski sheaf of meromorphic functions `𝒦_{T.left}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.10.5: if every weakly associated point of the representable algebraic space
`ofOver T` has codimension `0` and `ofOver T` satisfies Morphisms of Spaces Lemma 67.49.1,
then `𝒦_{ofOver T}` is isomorphic, as a quasi-coherent `𝒪`-algebra, to the étale
`𝒪`-algebra associated to `𝒦_{T.left}`. -/
@[stacks 0EN7]
theorem meromorphicFunctionSheaf_isIsomorphic_associated {S : Scheme.{u}} (T : Over S)
    [HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)]
    (hweak : (ofOver T).weakAss ⊆ codimZeroPoints (ofOver T)) :
    IsIsomorphic (Under.mk (toMeromorphicFunctionSheafHom (ofOver T)))
      (Under.mk (associatedToMeromorphicFunctionSheafHom T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
