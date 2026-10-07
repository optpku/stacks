module

public import ReasLib.CategoryTheory.Adjunction.EpiMono
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.15.1 (04DA): the counit is pointwise epic exactly when the right adjoint reflects
epimorphisms. -/
@[stacks 04DA "counit criterion"]
#check @Adjunction.counit_epi_iff_reflectsEpimorphisms

/- Lemma 18.15.1 (04DA) (2): under these equivalent conditions, the right adjoint is faithful. -/
@[stacks 04DA "faithfulness"]
#check @Functor.faithful_of_reflectsEpimorphisms
