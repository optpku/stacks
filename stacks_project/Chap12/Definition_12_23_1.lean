module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Homology
import StacksCheckRecall

/-!
# Definition 12.23.1

Source-facing checks for filtered differential objects.  The canonical owner is a one-object
homological complex in the category of filtered objects; no parallel wrapper is introduced.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Definition 12.23.1 [012B]: a filtered differential object is a filtered object equipped with
a filtration-preserving square-zero endomorphism. -/
@[stacks 012B]
#check (HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/- The unique differential is a morphism of filtered objects, so preservation of every stage is
part of the canonical morphism API. -/
#check (K.d PUnit.unit PUnit.unit : K.X PUnit.unit ⟶ K.X PUnit.unit)

/- Its square-zero law is the ordinary homological-complex law. -/
#check HomologicalComplex.d_comp_d
