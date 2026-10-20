module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 65.11.1: let `S` be a scheme contained in `Sch_fppf`. Let `F` be a sheaf
on `(Sch/S)_fppf` such that there exists `U` in `Ob((Sch/S)_fppf)` and a map
`U ⟶ F` which is representable, surjective, and étale. Then `F` is an algebraic
space. -/
@[stacks 0BGQ] #check (AlgebraicGeometry.AlgebraicSpace.ofEtaleSurjective_spec :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F →
    ∀ {U : Over S} (p : yoneda.obj U ⟶ F),
      (over (@Etale ⊓ @Surjective)).presheaf p →
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
          ∃ (V : Over S) (q : yoneda.obj V ⟶ F),
            (over (@Etale)).presheaf q ∧
              Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q)
