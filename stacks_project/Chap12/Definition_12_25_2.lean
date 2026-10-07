module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (F : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
variable (K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
variable (f : K ⟶ L)

/- Definition 12.25.2 (1) [0131]: weak convergence of either double-complex spectral sequence
uses the filtered-complex comparison with the infinity page. -/
@[stacks 0131]
#check (FilteredComplex.Cohomology.Convergence.IsWeak F E : Prop)

/- Definition 12.25.2 (2) [0131]: abutment additionally requires the induced cohomology
filtration to be separated and exhaustive. -/
@[stacks 0131]
#check (FilteredComplex.Cohomology.Convergence.Abuts F E : Prop)

/- Definition 12.25.2 (3) [0131]: convergence additionally records regularity and completeness
of the induced cohomology filtration. -/
@[stacks 0131]
#check (FilteredComplex.Cohomology.Convergence.Converges F E : Prop)

/- The first and second spectral sequences use the two canonical filtered totals. -/
#check (HomologicalComplex₂.First.Filtration.total K : FilteredComplex C)
#check (HomologicalComplex₂.Second.Filtration.total K : FilteredComplex C)

/- Double-complex morphisms act on both filtered totals without choosing spectral sequences. -/
#check (HomologicalComplex₂.First.Filtration.Map.hom f :
  HomologicalComplex₂.First.Filtration.total K ⟶ HomologicalComplex₂.First.Filtration.total L)
#check (HomologicalComplex₂.Second.Filtration.Map.hom f :
  HomologicalComplex₂.Second.Filtration.total K ⟶ HomologicalComplex₂.Second.Filtration.total L)
