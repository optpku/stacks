module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Presentation
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Transport
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical overlap formula for family descent data

The canonical descent datum is owned by `Pseudofunctor.DescentData`.  This file records the
chosen-overlap presentation of its comparison isomorphism as a single reusable bridge theorem.
The presentation-specific names stay in `SemiRepresentableFamily.Over`; the descent datum itself
is the canonical `DescentDatum` owner.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {p : S ⥤ C}
variable (hc : Functor.Cleavage p)
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U}

namespace DescentDatum.Canonical

/-- Lemma 8.3.6: on any chosen pullback of two family members, the comparison of the canonical
descent datum is the inverse first composition comparison, followed by transport along the
pullback equation, followed by the second composition comparison. -/
@[stacks 026D "comparison on an arbitrary chosen overlap"]
theorem overlapIso
    (X : p.Fiber U) (i j : 𝒰.index)
    (sq : ChosenPullback (𝒰.obj i).hom (𝒰.obj j).hom) :
    ((DescentDatum.canonicalFunctor hc 𝒰).obj X).iso
        sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
      (Cleavage.Reindex.compIsoApp hc (𝒰.obj i).hom sq.p₁ X).symm ≪≫
        Cleavage.Reindex.congrIsoApp hc sq.condition X ≪≫
        Cleavage.Reindex.compIsoApp hc (𝒰.obj j).hom sq.p₂ X := sorry

/-- In a chosen overlap presentation, the `canᵢⱼ` morphism is the morphism underlying the
canonical composition-comparison formula.  This is the presentation-facing form of
`DescentDatum.Canonical.overlapIso`. -/
@[stacks 026D "chosen-presentation overlap morphism"]
theorem presentationHom
    (P : 𝒰.OverlapPresentation) (X : p.Fiber U) (i j : 𝒰.index) :
    ((DescentDatum.Chosen.fromCanonical hc P).obj
        ((DescentDatum.canonicalFunctor hc 𝒰).obj X)).hom i j =
      ((Cleavage.Reindex.compIsoApp hc (𝒰.obj i).hom (P.fst i j) X).symm ≪≫
        Cleavage.Reindex.congrIsoApp hc (P.fst_hom_eq_snd_hom i j) X ≪≫
        Cleavage.Reindex.compIsoApp hc (𝒰.obj j).hom (P.snd i j) X).hom := sorry

section CanonicalChoice

variable [𝒰.toPresieve.HasPairwisePullbacks]

/-- The arbitrary-overlap formula specialized to the pullback selected by the ambient
`Presieve.HasPairwisePullbacks` instance. -/
@[stacks 026D "canonical chosen-overlap comparison"]
theorem chosenOverlapIso (X : p.Fiber U) (i j : 𝒰.index) :
    ((DescentDatum.canonicalFunctor hc 𝒰).obj X).iso
        (𝒰.overlapMap i j) (𝒰.fst i j) (𝒰.snd i j)
        (𝒰.fst_hom i j) (𝒰.snd_hom i j) =
      (Cleavage.Reindex.compIsoApp hc (𝒰.obj i).hom (𝒰.fst i j) X).symm ≪≫
        Cleavage.Reindex.congrIsoApp hc (𝒰.fst_hom_eq_snd_hom i j) X ≪≫
        Cleavage.Reindex.compIsoApp hc (𝒰.obj j).hom (𝒰.snd i j) X := sorry

end CanonicalChoice

end DescentDatum.Canonical

end CategoryTheory
