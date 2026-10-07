module

public import stacks_project.Chap35.Lemma_35_26_3_SourceLocus
public import stacks_project.Chap35.Lemma_35_32_4
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus.Etale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace CategoryTheory.MorphismProperty

/- Lemma 35.32.9: in a commutative square of schemes, if both vertical maps are
étale at the selected points, then membership in the source locus of an
étale-local-on-source-and-target property is preserved and reflected. -/
@[stacks 0CEZ]
#check (CategoryTheory.MorphismProperty.mem_sourceLocus_iff_of_etaleAt_commSq :
  ∀ (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    {X' X Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (g : Y' ⟶ Y) (f : X ⟶ Y), CommSq f' g' g f → ∀ (x' : X'),
      g'.EtaleAt x' → g.EtaleAt (f' x') →
        (g' x' ∈ P.sourceLocus f ↔ x' ∈ P.sourceLocus f'))

end CategoryTheory.MorphismProperty
