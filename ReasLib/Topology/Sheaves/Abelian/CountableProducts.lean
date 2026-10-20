module

public import Mathlib.Topology.UniformSpace.Real
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.Opposite
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Countable products of abelian sheaves

Abelian sheaves on the real line give the standard counterexample to exactness of countable
products.  The opposite category consequently fails countable `AB4`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

/-- The universe-polymorphic sheafification owner specialized to abelian groups on the real
line.  Naming this specialization lets typeclass search recover the coefficient universe. -/
noncomputable instance realLineAddCommGrpHasSheafify :
    HasSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} :=
  TopCat.addCommGrpHasSheafify (TopCat.of ℝ)

/-- Countable products of abelian sheaves on the real line are not exact. -/
@[stacks 0AMH]
theorem realLine_not_countableAB4Star :
    ¬ CountableAB4Star (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) := sorry

/-- Countable coproducts in the opposite of abelian sheaves on the real line are not exact. -/
theorem realLineOpposite_not_countableAB4 :
    ¬ CountableAB4 ((TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))ᵒᵖ) := sorry

end TopCat.Sheaf
