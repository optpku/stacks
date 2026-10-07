module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Presentation
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Flat Freely Presented Cochain Differential Graded Algebras

This leaf relates boundedness of the underlying cochain complex of a freely
presented cochain differential graded algebra to its K-flatness.
-/

noncomputable section

universe u v

namespace CochainDGAlgebra.Free

variable {R : Type u} [CommRing R]

namespace Presentation

/-- A bounded-above freely presented cochain differential graded algebra is K-flat. -/
@[stacks 06YQ "free-presentation specialization"]
theorem isKFlat_of_boundedAbove
    {A : CochainDGAlgebra R} (P : Presentation A)
    (hbounded : CochainComplex.minus (ModuleCat R) A.toCochainComplex) :
    A.IsKFlat := sorry

end Presentation

end CochainDGAlgebra.Free
