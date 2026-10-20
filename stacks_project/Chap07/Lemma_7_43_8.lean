module

public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.Topos.ClosedImmersion.Exactness
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.43.8

The generic fully-faithful and reflection consequences belong to the
left-exact-adjunction API.  ReasLib's closed-immersion leaf adds only the
three preservation instances not implied by an embedding alone.
-/

@[expose] public section

/- Lemma 7.43.8 (08M1) (1): direct image of a closed immersion is fully
faithful. -/
@[stacks 08M1 "(1)"] #check @CategoryTheory.LeftExactAdjunction.IsEmbedding.pushforwardFullyFaithful

/- Lemma 7.43.8 (08M1) (2): direct image preserves epimorphisms. -/
@[stacks 08M1 "(2)"] #check @CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion.pushforwardPreservesEpimorphisms

/- Lemma 7.43.8 (08M1) (3): direct image preserves coequalizers. -/
@[stacks 08M1 "(3)"] #check @CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion.pushforwardPreservesCoequalizers

/- Lemma 7.43.8 (08M1) (4): direct image preserves pushouts. -/
@[stacks 08M1 "(4)"] #check @CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion.pushforwardPreservesPushouts

/- Lemma 7.43.8 (08M1) (5): direct image reflects monomorphisms. -/
@[stacks 08M1 "(5)"] #check @CategoryTheory.LeftExactAdjunction.IsEmbedding.pushforwardReflectsMonomorphisms

/- Lemma 7.43.8 (08M1) (6): direct image reflects epimorphisms. -/
@[stacks 08M1 "(6)"] #check @CategoryTheory.LeftExactAdjunction.IsEmbedding.pushforwardReflectsEpimorphisms

/- Lemma 7.43.8 (08M1) (7): direct image reflects isomorphisms. -/
@[stacks 08M1 "(7)"] #check @CategoryTheory.LeftExactAdjunction.IsEmbedding.pushforwardReflectsIsomorphisms
