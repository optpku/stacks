/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Dimension
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Finiteness

/-!
@stack 018V

# Finite coskeleton-degree comparisons

Binary coproducts form the copowers indexed by `Δ[q]` and `sk n Δ[q]`; finite limits
form the objectwise coskeleton.  This leaf specializes the assumption-minimal comparison in
`InternalHom.Coskeleton` to an arbitrary explicit representation of the internal-hom presheaf;
it does not choose a representing object from an existence proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom.coskeleton.degree

variable {C : Type u} [Category.{v} C]
variable [HasBinaryCoproducts C] [HasFiniteLimits C]

/-- Under finite-limit and binary-coproduct hypotheses, degree `q` of the `n`-coskeleton is
canonically degree zero of every explicit representation of the internal-hom presheaf from
`sk n Δ[q]`. -/
@[stacks 018V "finite coskeleton-degree internal-hom comparison"]
noncomputable def ofRepresentableBy.iso (n q : ℕ) (V : SimplicialObject C)
    {M : SimplicialObject C}
    (R : (internalHom.presheaf ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).RepresentableBy M) :
    ((truncation n).obj V).coskeleton.obj (op (SimplexCategory.mk q)) ≅
      M.obj (op (SimplexCategory.mk 0)) :=
  zero.ofRepresentableBy.iso n q V R

end CategoryTheory.SimplicialObject.internalHom.coskeleton.degree
