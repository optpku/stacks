module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Flat Degree-Zero Cochain Differential Graded Algebras

This leaf characterizes K-flatness of the cochain DGA canonically associated to an ordinary
algebra in terms of flatness of its underlying module over the ground ring.
-/

noncomputable section

universe u v

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- An ordinary algebra, regarded as a DGA concentrated in degree zero, is K-flat exactly when
its underlying module over the base ring is flat. -/
@[stacks 09SC "flat ordinary algebra as a K-flat degree-zero DGA"]
theorem ofAlgebra_isKFlat_iff (A : Type v) [Ring A] [Algebra R A] :
    (ofAlgebra R A).IsKFlat ↔ Module.Flat R A := sorry

/-- A flat ordinary algebra gives a K-flat degree-zero DGA. -/
@[stacks 09SC "flat ordinary algebra gives a K-flat degree-zero DGA"]
theorem ofAlgebra_isKFlat (A : Type v) [Ring A] [Algebra R A] [Module.Flat R A] :
    (ofAlgebra R A).IsKFlat := sorry

end CochainDGAlgebra
