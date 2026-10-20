/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.KInjective.DerivedProduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.5

The mathematical core separates into closure of K-injectives under a supplied
limit cone and preservation of a K-injective product by derived localization.
The former is intentionally not specialized to a chosen product model.
-/

/- Lemma 13.31.5 (Stacks 0BK6) (1): a supplied product cone of K-injective
cochain complexes has K-injective vertex. -/
@[stacks 0BK6] #check @CochainComplex.IsKInjective.of_isLimit

/- Lemma 13.31.5 (Stacks 0BK6) (2): derived localization preserves products
modelled by K-injective cochain complexes. -/
@[stacks 0BK6] #check @CategoryTheory.DerivedCategory.Product.q_preservesProduct_of_kInjective
