/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Trace
import StacksCheckRecall

open CategoryTheory
open scoped Ring

universe u

/- Proposition 64.10.2. Let `K` be a perfect object of `D(R)` and `f` an
endomorphism of `K` in `D(R)`. Then the trace `Tr(f) ∈ R♮` is well defined:
for any bounded finite-projective representative `P` with `e : Q.obj P ≅ K`
and any chain map `fP : P ⟶ P` representing `e.hom ≫ f ≫ e.inv`, one has
`hK.traceNatural f = CochainComplex.IsBoundedFiniteProjective.traceNatural fP`. -/
@[stacks 03TI] #check (DerivedCategory.IsPerfect.traceNatural_spec :
    ∀ {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat R)} (hK : DerivedCategory.IsPerfect K)
    (f : End K) (P : CochainComplex (ModuleCat R) ℤ)
    [P.IsBoundedFiniteProjective] (e : DerivedCategory.Q.obj P ≅ K)
    (fP : P ⟶ P) (hfP : DerivedCategory.Q.map fP = e.hom ≫ f ≫ e.inv),
    hK.traceNatural f =
      CochainComplex.IsBoundedFiniteProjective.traceNatural fP)
