/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
# Lemma 13.22.2

The Grothendieck spectral sequence is owned by the neutral ReasLib API.  Its realization keeps
the associated filtered complex, page-two comparison, abutment comparison, boundedness, finite
filtrations, and convergence separately accessible; the map layer records naturality.
-/

open CategoryTheory

/- Lemma 13.22.2 (Grothendieck spectral sequence): for left-exact functors
`A ⥤ B ⥤ C` between abelian categories with enough injectives in `A` and `B`, if `F`
sends injective objects to bounded-below right-acyclic objects for `G`, every `X : D⁺(A)` admits
a bounded convergent spectral sequence with
page-two terms `pageTwo G (Bounded.functor F) X p q`, and degree-`n` abutment
`abutment (Bounded.functor (F ⋙ G)) X n`. -/
@[stacks 015N]
#check @Functor.RightDerived.Grothendieck.nonempty

/- The canonical specialization uses the total bounded-below right-derived functors of `F` and
`F ⋙ G`. -/
#check @Functor.RightDerived.Grothendieck.canonical

/- The page-two and abutment target objects are reusable independently of a chosen realization. -/
#check @Functor.RightDerived.Grothendieck.pageTwoFunctor
#check @Functor.RightDerived.Grothendieck.pageTwo
#check @Functor.RightDerived.Grothendieck.abutmentFunctor
#check @Functor.RightDerived.Grothendieck.abutment

/- A realization exposes the chosen filtered-complex association and each convergence property. -/
#check @FilteredComplex.SpectralSequence.Realization.isAssociated
#check @Functor.RightDerived.Grothendieck.SpectralSequence.pageTwoIso
#check @Functor.RightDerived.Grothendieck.SpectralSequence.toWithAbutment
#check @FilteredComplex.SpectralSequence.Realization.WithAbutment.abutmentIso
#check @FilteredComplex.SpectralSequence.Realization.bounded
#check @FilteredComplex.SpectralSequence.Realization.finite
#check @FilteredComplex.SpectralSequence.Realization.converges

/- The functorial existence theorem and equation-form naturality API support downstream maps. -/
#check @Functor.RightDerived.Grothendieck.existsMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.ext
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.ext_filteredMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.toWithAbutmentMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.toAssociationHom
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.toAssociationHom_hom
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.pageTwo_hom
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.abutment_hom
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.id
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.comp
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.id_filteredMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.id_sequenceMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.comp_filteredMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.comp_sequenceMap
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.toAssociationHom_id
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.toAssociationHom_comp
#check @Functor.RightDerived.Grothendieck.SpectralSequence.Map.toAssociationHom_reindex
#check @Functor.RightDerived.Grothendieck.pageTwoMap_id
#check @Functor.RightDerived.Grothendieck.pageTwoMap_comp
#check @Functor.RightDerived.Grothendieck.abutmentMap_id
#check @Functor.RightDerived.Grothendieck.abutmentMap_comp
