/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductCompatibility
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.31.6:
- primary domain: braided monoidal commutativity for the relative derived cup product on
  `D(𝒪_X)` and `D(𝒪_Y)`;
- sampled owner declarations:
  `CategoryTheory.Adjunction.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`,
  `CategoryTheory.BraidedCategory` via `β_`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the cup product is owned by
  `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`, specialized to the canonical
  ambient tensor `curriedTensor` on the derived categories of module sheaves on ringed spaces, so
  this file should reuse that owner directly rather than rebuilding a second ringed-space theorem
  with the same interface; the commutativity constraint is therefore the braided owner morphism
  `β_`, not an arbitrary chosen swap isomorphism;
- primitive data: the adjunction `Lf^* ⊣ Rf_*`, the pullback-tensor comparison
  `Lf^*(A ⊗ B) ≅ Lf^* A ⊗ Lf^* B`, and its braiding-compatibility square;
- derived API: the relative cup-product morphism and its `CommSq` compatibility with the source
  and target braidings.

Source/core/bridge triage:
- `source-facing`: the ringed-space commutativity square for relative cup products;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`;
- `bridge/view`: this file is recall-only, since the source-facing statement is exactly the
  categorical owner theorem specialized to derived categories of module sheaves on ringed spaces.
-/

/- Lemma 20.31.6 is exactly the categorical owner theorem
`CategoryTheory.relativeDerivedCupProduct_commutative_commSq`: for the ringed-space derived
pullback/pushforward adjunction `Lf^* ⊣ Rf_*`, the relative cup product of Remark 20.28.7 is
compatible with the braidings on source and target, provided the pullback-tensor comparison
intertwines those braidings. -/
@[stacks 0FP5] #check @CategoryTheory.Adjunction.relativeDerivedCupProduct
#check @CategoryTheory.Adjunction.relativeDerivedCupProduct_spec
#check @CategoryTheory.relativeDerivedCupProduct_commutative_commSq

end AlgebraicGeometry.RingedSpace
