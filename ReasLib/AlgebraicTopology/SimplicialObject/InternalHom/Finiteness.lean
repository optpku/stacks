module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Constant
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Degreewise
public import ReasLib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
@stack 017L

# Finite simplicial sets and internal mapping objects

Degreewise finiteness, the required simplicial copowers, and an eventual dimension bound give the
finite-limit representability criterion for simplicial internal mapping objects. A vertex and
binary coproducts are one convenient way to construct those copowers, not part of the core
criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type uC} [Category.{vC} C]
variable [HasFiniteLimits C]
variable (U : SSet.{uS}) [U.ObjFinite] [HasCopowers U C]
variable (T : SimplicialObject C)

namespace presheaf

/-- A degreewise finite simplicial set with the required copowers and an eventual dimension bound
admits an internal mapping object into every simplicial object of a category with finite limits. -/
@[stacks 017L]
theorem isRepresentable.ofEventuallyDegenerate
    [hU : U.EventuallyDegenerate] :
    (presheaf U T).IsRepresentable := sorry

/-- A finite nonempty simplicial set admits an internal mapping object into every simplicial
object of a category with binary coproducts and finite limits. -/
@[stacks 017L "finite simplicial-set internal hom"]
theorem isRepresentable.ofFinite [HasBinaryCoproducts C]
    (U : SSet.{uS}) [U.Finite] [U.Nonempty]
    (T : SimplicialObject C) :
    (presheaf U T).IsRepresentable := sorry

end presheaf

end CategoryTheory.SimplicialObject.internalHom

namespace CategoryTheory.SimplicialObject.HasInternalHoms

variable {C : Type uC} [Category.{vC} C] [HasFiniteLimits C]

/-- A finite, nonempty, eventually degenerate indexing simplicial set has internal homs in every
category with finite limits and binary coproducts.  This is the canonical instance form of the
finite representability criterion; it supplies only a proposition-valued existence fact, so it
does not choose public mapping-object data. -/
@[stacks 017L "finite eventually degenerate simplicial-set internal homs"]
noncomputable instance (priority := 100) ofEventuallyDegenerate (U : SSet.{uS})
    [HasBinaryCoproducts C] [U.ObjFinite] [U.Nonempty] [U.EventuallyDegenerate] :
    HasInternalHoms U C :=
  fun T => internalHom.presheaf.isRepresentable.ofEventuallyDegenerate U T

end CategoryTheory.SimplicialObject.HasInternalHoms
