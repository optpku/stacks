module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.QuasiCoherent
public import ReasLib.CategoryTheory.Pro.Sequential.Realization
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace DifferentialGradedModule.InverseSystem.Derived

section


variable {R : Type u} [CommRing R]
variable {A B : ℕᵒᵖ ⥤ CochainDGAlgebra.{u, v} R}
variable {r : CategoryTheory.Pro.SequentialHom A B}

/- The representative is an actual morphism between the pro-objects of the two DGA systems. -/
#check
  (r.toHom : CochainDGAlgebra.InverseSystem.proObject A ⟶
    CochainDGAlgebra.InverseSystem.proObject B)

/- Lemma 24.35.1 (tag 0GZH), source categories: `QC A` and `QC B` are now cut out inside the
global localizations `D(ℕ, A)` and `D(ℕ, B)`.  The remaining declaration must be the canonical
pullback associated to the displayed pro-morphism; no arbitrary fiberwise functor is accepted as
that construction. -/
@[stacks 0GZH "global QC categories for pro-DGA pullback"]
#check (QC A ⥤ QC B)

end


end DifferentialGradedModule.InverseSystem.Derived
