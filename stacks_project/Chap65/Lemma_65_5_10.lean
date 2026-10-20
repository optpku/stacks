module

public import ReasLib.CategoryTheory.RepresentablePresheaf.RelativelyRepresentable
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u v

variable (X : AlgebraicGeometry.ChosenBigSite.{u, v} AlgebraicGeometry.Scheme.fppfPrecoverage)
  (S : X.carrier) (F : (Over S)ᵒᵖ ⥤ Type v)

/- Lemma 65.5.10: for a presheaf of sets on `(Sch/S)_fppf`, representability of its diagonal,
representability of every Yoneda section, and representability of every pairwise section pullback
are equivalent. -/
@[stacks 025W] #check (CategoryTheory.Functor.relativelyRepresentable.diag_tfae
      (C := Over S) (hasBinaryProducts := X.sliceHasBinaryProducts S) (F := F) :
    [yoneda.relativelyRepresentable (diag F),
      ∀ (U : Over S) (ξ : yoneda.obj U ⟶ F),
        yoneda.relativelyRepresentable ξ,
      ∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F)
        (ξ' : yoneda.obj V ⟶ F),
        (pullback ξ ξ').IsRepresentable].TFAE)
