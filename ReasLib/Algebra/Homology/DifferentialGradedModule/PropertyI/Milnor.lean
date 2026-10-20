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

/-- The Milnor product sequence of a property I filtration is short exact.  This is the generic
`SequentialInverseFiltration.Milnor.shortExact_of_map_isSplitEpi` applied to the faithful additive
functor forgetting only the differential: it preserves products, and condition (2) of property (I)
says that it sends every successor transition `I/F_{n+1}I ⟶ I/F_nI` to a split epimorphism. -/
theorem milnorShortComplex_shortExact (F : Filtration A I) :
    F.milnorShortComplex.ShortExact :=
  SequentialInverseFiltration.Milnor.shortExact_of_map_isSplitEpi F.underlying
    (DifferentialGradedModule.forgetToGraded A) F.admissible

/-- Lemma 22.21.1 (09KR): the Milnor product sequence associated to a property I filtration is
admissibly short exact.  Its ordinary short exactness is `milnorShortComplex_shortExact`, while
admissibility of the difference map is `milnorDifferenceMap_isAdmissibleEpi`. -/
@[stacks 09KR]
theorem milnorIsAdmissibleShortExact (F : Filtration A I) :
    DifferentialGradedModule.IsAdmissibleShortExact F.milnorShortComplex := sorry

end DifferentialGradedModule.PropertyI.Filtration
