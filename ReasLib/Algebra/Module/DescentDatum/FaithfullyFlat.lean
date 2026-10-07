module

public import ReasLib.Algebra.Module.DescentDatum.BaseChange

/-!
# Effective module descent along faithfully flat algebras

Module descent data along a faithfully flat algebra are effective, and their
canonical scalar-extension reconstruction maps are isomorphisms.
-/

@[expose] public section

noncomputable section

namespace Module.DescentDatum

universe u

variable {R A N : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Module.FaithfullyFlat R A]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]

/-- Every module descent datum along a faithfully flat algebra is effective. -/
theorem isEffective_of_faithfullyFlat (D : DescentDatum R A N) :
    D.IsEffective := sorry

/-- The canonical reconstruction from the scalar extension of the invariant
module of a faithfully flat descent datum is an isomorphism. -/
theorem reconstruction_isIso_of_faithfullyFlat (D : DescentDatum R A N) :
    CategoryTheory.IsIso D.reconstruction :=
  (D.isEffective_iff_isIso_reconstruction).mp D.isEffective_of_faithfullyFlat

end Module.DescentDatum
