module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.RepresentableSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 65.3.5: if `S` is a scheme, `F` and `G` are functors `(Over S)ᵒᵖ ⥤ Type u`
on `(Sch/S)_fppf`, and `a : F ⟶ G` is a representable transformation of functors, then
`G` being a sheaf for `Scheme.fppfTopology.over S` implies that `F` is a sheaf. -/
@[stacks 02WD] #check
  (AlgebraicGeometry.isSheaf_fppfTopology_over_of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      yoneda.relativelyRepresentable a →
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) G →
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
