/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_9_3_Induction

/-!
# Induction on a collection of spaces-étale objects

A property of a collection `B` of objects of `X_spaces,étale` that holds for affine
objects, is closed under quasi-compact open subspaces, and is preserved by elementary
distinguished squares, with the stated size conditions, holds for every member of `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A property `P` of a collection `B` of objects of `X_spaces,étale` holds for every
member of `B` whenever every member of `B` is quasi-compact and quasi-separated, `B` is
closed under quasi-compact open subspaces, every affine object of the site lies in `B`
and satisfies `P`, and `P` is preserved by elementary distinguished squares
`(U ⊂ W, f : V ⟶ W)` with `W` in `B`, `U` quasi-compact, `V` affine, and `P` true on
`U`, `V`, and `U ×_W V`. -/
theorem qcqsSpacesEtale_induction_mem {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (B : Set (spacesEtaleSite X)) (P : spacesEtaleSite X → Prop)
    (h_isQuasiCompact : ∀ W ∈ B, IsQuasiCompact W.left)
    (h_isAbsolutelyQuasiSeparated : ∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left)
    (h_open : ∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
      [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B)
    (h_affine_mem : ∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B)
    (h_affine : ∀ (V : spacesEtaleSite X) [IsAffine V.left], P V)
    (h_square : ∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      W ∈ B → P U → P V → P (spacesEtaleSite.fiber j f) → P W)
    (W : spacesEtaleSite X) (hW : W ∈ B) : P W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
