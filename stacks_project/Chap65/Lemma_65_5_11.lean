module

public import ReasLib.CategoryTheory.MorphismProperty.Representable.PresheafDiagonal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u v

variable (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (S : X.carrier)
  (P : MorphismProperty Scheme.{u})
  [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
  (F : (Over S)ᵒᵖ ⥤ Type u)

/- Lemma 65.5.11: for a presheaf of sets on the chosen fppf-site slice, if every
pairwise pullback of Yoneda sections is representable and its comparison to the
product has the scheme morphism property `P`, then the diagonal is representable
and has `P`. The property `P` is stable under base change and fppf local on the base.
The property on the slice is pulled back along its actual functor to schemes. -/
@[stacks 0CB7] #check (CategoryTheory.MorphismProperty.presheaf_diag
    (C := Over S) (hasBinaryProducts := X.sliceHasBinaryProducts S)
    (P := P.inverseImage (ChosenBigSite.sliceToScheme X S)) (F := F) :
  (∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
    (pullback ξ ξ').IsRepresentable) →
  (∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
    (P.inverseImage (ChosenBigSite.sliceToScheme X S)).presheaf
      (prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ'))) →
  (P.inverseImage (ChosenBigSite.sliceToScheme X S)).presheaf (diag F))

#check (CategoryTheory.MorphismProperty.presheaf_diag_iff
    (C := Over S) (hasBinaryProducts := X.sliceHasBinaryProducts S)
    (P := P.inverseImage (ChosenBigSite.sliceToScheme X S)) (F := F) :
  (P.inverseImage (ChosenBigSite.sliceToScheme X S)).presheaf (diag F) ↔
    ∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      (pullback ξ ξ').IsRepresentable ∧
        (P.inverseImage (ChosenBigSite.sliceToScheme X S)).presheaf
          (prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ')))
