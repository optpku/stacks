/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Abelian
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI
public import ReasLib.CategoryTheory.Filtration.SequentialInverse.Milnor

/-!
# Milnor product sequences for property I filtrations
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.PropertyI.Filtration

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {I : DifferentialGradedModule.{u, v} A}

/-- The Milnor product short complex associated to a property I filtration. -/
abbrev milnorShortComplex (F : Filtration A I) :
    ShortComplex (DifferentialGradedModule.{u, v} A) :=
  SequentialInverseFiltration.Milnor.shortComplex
    (C := DifferentialGradedModule.{u, v} A) F.underlying

/-- The Milnor difference map of a property I filtration is admissibly epic: after forgetting the
differential, it is the image of a product-preserved Milnor difference map whose successor
transitions are split epimorphisms. -/
theorem milnorDifferenceMap_isAdmissibleEpi (F : Filtration A I) :
    DifferentialGradedModule.IsAdmissibleEpi F.milnorShortComplex.g := sorry

/-- Lemma 22.21.1 (09KR): the Milnor product sequence associated to a property I filtration is
admissibly short exact.  Its ordinary short exactness is the generic sequential-inverse-filtration
theorem, while admissibility is supplied by the split-epic forgetful Milnor bridge. -/
@[stacks 09KR]
theorem milnorIsAdmissibleShortExact (F : Filtration A I) :
    DifferentialGradedModule.IsAdmissibleShortExact F.milnorShortComplex := sorry

end DifferentialGradedModule.PropertyI.Filtration
