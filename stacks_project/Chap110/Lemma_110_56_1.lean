module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FlatCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 110.56.1: an fpqc sheaf with representable diagonal admits a
surjective, flat, universally open, quasi-compact scheme cover but no
representable surjective étale atlas. Since fpqc descent implies fppf descent,
the negative atlas clause expresses precisely non-algebraicity. -/
@[stacks 078F]
#check
  (AlgebraicGeometry.AlgebraicSpace.exists_fpqcSheaf_flatCover_no_etaleAtlas :
    ∃ (F : Scheme.{u}ᵒᵖ ⥤ Type u),
      Presheaf.IsSheaf Scheme.fpqcTopology F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
        (∃ (U : Scheme.{u})
            (p : yoneda.obj U ⟶ F),
          ((@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
              @AlgebraicGeometry.UniversallyOpen ⊓ @AlgebraicGeometry.QuasiCompact) :
              MorphismProperty Scheme).presheaf p) ∧
        ¬ (∃ (V : Scheme.{u})
            (q : yoneda.obj V ⟶ F),
          ((@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective) :
              MorphismProperty Scheme).presheaf q))
