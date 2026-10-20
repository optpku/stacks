/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.IsAlgClosed.Polynomial
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable (F : Type u) [Field F]

/- Domain triage:
- primary domain: algebraically closed fields, expressed through polynomial factorization and root
  existence criteria;
- sampled owner declarations: `IsAlgClosed`, `IsAlgClosed.exists_root`,
  `IsAlgClosed.of_exists_root`, and `IsAlgClosed.degree_eq_one_of_irreducible`;
- core/canonical owner abstraction: `IsAlgClosed F`, with the reusable equivalences in
  `IsAlgClosed.polynomialTFAE`;
- layer: canonical check, since the shared owner now exposes the complete list of equivalent
  polynomial characterizations;
- primitive data: only the field `F`;
- derived API: the irreducible-linear, nonconstant-root, and nonconstant-splitting criteria below.

The source item therefore checks the shared theorem directly rather than retaining chapter-owned
copies of its reusable component equivalences.
-/

/- Lemma 9.10.2: for a field `F`, the following are equivalent: `F` is algebraically closed,
every irreducible polynomial over `F` is linear, every nonconstant polynomial over `F` has a
root, and every nonconstant polynomial over `F` splits as a product of linear factors. -/
@[stacks 09GR]
#check (IsAlgClosed.polynomialTFAE F :
  List.TFAE [
      IsAlgClosed F,
      ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits
    ])

/- Companion checks expose the fine-grained rewrite API without chapter-owned wrappers. -/
#check IsAlgClosed.iffForallIrreducibleDegreeEqOne
#check IsAlgClosed.iffForallNonconstantExistsRoot
#check IsAlgClosed.iffForallNonconstantSplits

end
