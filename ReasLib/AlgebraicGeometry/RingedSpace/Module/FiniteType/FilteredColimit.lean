/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.FilteredColimit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Finite-type module sheaves in filtered colimits on ringed spaces

This file is the source-facing ringed-space specialization of the coefficient-independent module
sheaf owner.  Directed systems are presented by preorders, as in the Stacks Project statement.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules.FilteredColimit

variable {X : RingedSpace.{u}} [CompactSpace X]
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (ℱ : I ⥤ X.Modules)

/- Lemma 17.9.7 (01BB) (1): the ringed-space statement is the generic module-sheaf owner
specialized to `X.ringCatSheaf`. -/

/- Lemma 17.9.7 (01BB) (2): the monomorphism specialization is also owned generically. -/

end AlgebraicGeometry.RingedSpace.Modules.FilteredColimit
