module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
public import stacks_project.Chap65.Example_65_14_7_ArtinSchreier

/-!
# The algebraic space given by the rational absolute Galois quotient

The quotient, its Galois action, and its atlas are provided by their algebraic-geometry
owner. The field compatibility names remain available to direct consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.cover :
  Over AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.base)

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action :
  AlgebraicNumbers.gal →*
    Aut AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.cover)

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action_hom :
  ∀ σ : AlgebraicNumbers.gal,
    (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action σ).hom.left =
      AlgebraicGeometry.FieldExtension.Galois.baseAut ℚ AlgebraicNumbers.algebraicQ σ⁻¹)

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints :
  Sheaf
    (Scheme.fppfTopology.over AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.base)
    (Type 1))

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.atlas :
  (Scheme.fppfTopology.over AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.base).uliftYoneda.{1}.obj
      AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.cover ⟶
    AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints)

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints_spec :
  uliftYoneda.{1}.relativelyRepresentable
      (diag AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints.obj) ∧
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{1}
      AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.atlas.hom ∧
    Presheaf.IsLocallySurjective
      (Scheme.etaleTopology.over AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.base)
      AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.atlas.hom)
