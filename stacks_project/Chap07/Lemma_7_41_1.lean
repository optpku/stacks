module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Adjunction.EpiMono
public import ReasLib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.CategoryTheory.Sites.Topos.SurjectionLifting

/-!
# Exactness properties of pushforward

The source's set-valued surjections are modeled by
`CategoryTheory.Sheaf.IsLocallySurjective`.  When sheafification is available,
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi` identifies this with the
categorical `Epi` interface.  The resulting API has three independent owners:
adjunction consequences in `Adjunction`, local-surjectivity preservation in
`Sites.LocallySurjective`, and the inverse-image lifting property in
`Sites.Topos.SurjectionLifting`.
-/

@[expose] public section

/- Lemma 7.41.1 (04D6) (1): a fully faithful pushforward is faithful. -/
@[stacks 04D6 "(1)"] #check @CategoryTheory.Functor.FullyFaithful.faithful

/- Lemma 7.41.1 (04D6) (2): if every counit component is surjective, then the
right adjoint, hence the pushforward, is faithful. -/
@[stacks 04D6 "(2)"] #check @CategoryTheory.Sheaf.isLocallySurjective_iff_epi

@[stacks 04D6 "(2)"] #check @CategoryTheory.Adjunction.faithful_R_of_counit_epi

/- Lemma 7.41.1 (04D6) (3): an invertible counit makes the right adjoint fully
faithful, faithful, locally-surjective on counits, and reflective for monos,
epis, and isomorphisms. These are separate generic adjunction consequences,
rather than Chapter 7 wrapper declarations. -/
@[stacks 04D6 "(3)"] #check @CategoryTheory.Adjunction.FullyFaithful.right_iff_isIso_counit

@[stacks 04D6 "(3)"] #check @CategoryTheory.Adjunction.faithful_R_of_counit_epi

@[stacks 04D6 "(3)"] #check @CategoryTheory.Sheaf.isLocallySurjective_iff_epi

@[stacks 04D6 "(3)"] #check @CategoryTheory.Adjunction.reflectsEpimorphisms_of_counit_epi

@[stacks 04D6 "(3)"] #check @CategoryTheory.Adjunction.reflectsMonomorphisms_R_of_reflectsEpimorphisms

@[stacks 04D6 "(3)"] #check @CategoryTheory.Adjunction.reflectsIsomorphisms_R_of_reflectsEpimorphisms

/- Lemma 7.41.1 (04D6) (4): locally surjective counit components are
equivalent to the right adjoint reflecting epimorphisms. -/
@[stacks 04D6 "(4)"] #check @CategoryTheory.Adjunction.counit_isLocallySurjective_iff_reflectsEpimorphisms

/- Lemma 7.41.1 (04D6) (5): preserving either pushouts or coequalizers makes
the pushforward preserve surjections. -/
@[stacks 04D6 "(5)"] #check @CategoryTheory.Functor.preservesLocallySurjective_of_preservesPushouts

@[stacks 04D6 "(5)"] #check @CategoryTheory.Functor.preservesLocallySurjective_of_preservesCoequalizers

/- Lemma 7.41.1 (04D6) (6): preservation of surjections by pushforward is
equivalent to the source's lifting condition along inverse image. -/
@[stacks 04D6 "(6)"] #check @CategoryTheory.MorphismOfTopoiIn.HasSurjectionLifting.iff_preservesLocallySurjective

/- Lemma 7.41.1 (04D6) (7): reflection of epimorphisms by the right adjoint
also gives reflection of monomorphisms and, in a balanced category, of
isomorphisms. -/
@[stacks 04D6 "(7)"] #check @CategoryTheory.Adjunction.reflectsMonomorphisms_R_of_reflectsEpimorphisms

@[stacks 04D6 "(7)"] #check @CategoryTheory.Adjunction.reflectsIsomorphisms_R_of_reflectsEpimorphisms

/- Lemma 7.41.1 (04D6) (8): a right adjoint is fully faithful exactly when its
counit is invertible. -/
@[stacks 04D6 "(8)"] #check @CategoryTheory.Adjunction.FullyFaithful.right_iff_isIso_counit
