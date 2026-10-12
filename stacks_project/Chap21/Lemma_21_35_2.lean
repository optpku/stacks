/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.2

The objectwise derived internal-Hom isomorphism and its functoriality are already owned by the
generic braided closed-monoidal API.  The ringed-site derived category is only a specialization,
so this chapter item keeps no second construction or proof-local derived-category instance.
-/

/- Lemma 21.35.2 (08J9): the canonical isomorphism
`RHom(K, RHom(L, M)) ≅ RHom(K ⊗ L, M)`. -/
@[stacks 08J9 "internal-Hom tensor isomorphism"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso

@[stacks 08J9 "internal-Hom tensor naturality in the first variable"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_left

@[stacks 08J9 "internal-Hom tensor naturality in the second variable"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_middle

@[stacks 08J9 "internal-Hom tensor naturality in the target"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_right
