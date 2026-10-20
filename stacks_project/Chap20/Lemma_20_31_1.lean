/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.31.1:
- primary domain: relative derived cup products for the adjunction
  `Lf^* ⊣ RΓ(X, -)` on derived categories;
- sampled owner declarations:
  `CategoryTheory.Adjunction.relativeDerivedCupProduct`,
  `CategoryTheory.Adjunction.relativeDerivedCupProduct_spec`,
  `Adjunction.homEquiv`;
- source/core/bridge triage:
  `source-facing`: the global-sections specialization of the pullback-side description of the
    cup product;
  `core/canonical`: `CategoryTheory.Adjunction.relativeDerivedCupProduct_spec`;
  `bridge/view`: this chapter file is recall-only, since the source-facing statement is exactly
    the generic owner theorem viewed in the ringed-space setting.

Primitive data already live in the owner theorem: the adjunction, the pullback-tensor comparison,
and the adjoint-side transpose. The cup product and its specification are derived API from that
owner layer, so this file should reuse the owner theorem directly rather than keep a parallel
ringed-space wrapper. -/

/- Lemma 20.31.1 is exactly the ringed-space derived-global-sections specialization of the
canonical adjunction-side specification theorem. -/
@[stacks 0FP2] #check @CategoryTheory.Adjunction.rightAdjointTensorMapOf_spec
#check @CategoryTheory.Adjunction.relativeDerivedCupProduct
#check @CategoryTheory.Adjunction.relativeDerivedCupProduct_spec

end AlgebraicGeometry.RingedSpace
