module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 97.11.3. Restriction of scalars along a finite locally free morphism
preserves étale morphisms and étale surjections. -/
@[stacks 05YD] #check (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.instEtale_map :
  ∀ {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B)
    [AlgebraicSpace.Etale h] [AlgebraicSpace.FiniteLocallyFree g],
    Groupoids.Hom.Etale
      (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.mapGroupoids h f g))

#check (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.instSurjective_map :
  ∀ {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B)
    [AlgebraicSpace.Etale h] [AlgebraicSpace.Surjective h]
    [AlgebraicSpace.FiniteLocallyFree g],
    Groupoids.Hom.Surjective
      (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.mapGroupoids h f g))
