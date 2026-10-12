/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.RingTheory.Etale.FieldCriterion

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/-- The relative differential of every global function on a smooth proper scheme over a field
vanishes. -/
theorem globalSectionsDifferential_eq_zero {k : Type u} [Field k]
    (X : SchemeOverField k) [Smooth X.hom] [IsProper X.hom] :
    ∀ a : Γ(X.left, ⊤),
      ((d[X.hom.toShHom]).app (op (⊤ : X.left.Opens))).d a = 0 := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
