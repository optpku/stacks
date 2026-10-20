module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Induction
import StacksCheckRecall

/-!
# Induction on a collection of spaces-étale objects

A property of a collection `B` of objects of `X_spaces,étale` that holds for affine
objects, is closed under quasi-compact open subspaces, and is preserved by elementary
distinguished squares, with the stated size conditions, holds for every member of `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 75.9.4: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `B ⊂ Ob(X_spaces,étale)`. Let `P` be a property of the
elements of `B`. Under the stated quasi-compactness, quasi-separatedness, open-closure,
affine-membership, and distinguished-square hypotheses, `P` holds for every member of
`B`. -/
@[stacks 08GQ] #check
  (@AlgebraicGeometry.AlgebraicSpace.qcqsSpacesEtale_induction_mem :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (B : Set (spacesEtaleSite X)) (P : spacesEtaleSite X → Prop),
    (∀ W ∈ B, IsQuasiCompact W.left) →
    (∀ W ∈ B, IsAbsolutelyQuasiSeparated W.left) →
    (∀ {U W : spacesEtaleSite X} (j : U ⟶ W)
      [IsOpenImmersion j.left] [IsQuasiCompact U.left], W ∈ B → U ∈ B) →
    (∀ (V : spacesEtaleSite X) [IsAffine V.left], V ∈ B) →
    (∀ (V : spacesEtaleSite X) [IsAffine V.left], P V) →
    (∀ {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W)
      [IsElementaryDistinguishedSquare j.left f.left] [Etale f.left]
      [IsQuasiCompact U.left] [IsAffine V.left],
      W ∈ B → P U → P V → P (spacesEtaleSite.fiber j f) → P W) →
    ∀ (W : spacesEtaleSite X), W ∈ B → P W)
