/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Projection formula for perfect complexes on ringed sites

The categorical mate, canonical tensor owner, and perfectness bridge are maintained in
`ReasLib`; this file is the source-label recall.
-/

/- Lemma 21.50.1: for a morphism of commutative ringed-site presentations `f`, a perfect object
`K` on the target, and a derived module `E` on the source, the canonical morphism
`R(f)_* E ⊗ᴸ K ⟶ R(f)_* (E ⊗ᴸ L(f)^* K)` is an isomorphism. -/
@[stacks 0944]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.isIso_leftProjectionFormulaMate
