/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness
import StacksCheckRecall

/-!
# Lemma 18.27.5

The reusable API is stated for every abelian braided closed monoidal category.  Ringed-site
modules are a specialization, so this chapter file contains no local instance reconstruction.
-/

@[expose] public section

/- Lemma 18.27.5 (1) (0GMY): internal Hom is left exact in its contravariant source. -/
@[stacks 0GMY "(1)"]
#check @CategoryTheory.MonoidalClosed.InternalHom.mapOp_exact_of_exact_epi

/- Lemma 18.27.5 (2) (0GMY): internal Hom is left exact in its target. -/
@[stacks 0GMY "(2)"]
#check @CategoryTheory.MonoidalClosed.InternalHom.map_exact_of_exact_mono
