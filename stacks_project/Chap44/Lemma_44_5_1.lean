module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Representability

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupScheme

/- Lemma 44.5.1: a group-valued Zariski sheaf on schemes over a field is represented by a
group scheme if it contains a representable relatively open subfunctor whose translates by
`k`-points meet every field-valued point. -/
@[stacks 0B9Q] #check
  (AlgebraicGeometry.GroupScheme.representable_of_openSubfunctor :
    ∀ {k : Type u} [Field k] (G : (SchemeOverField k)ᵒᵖ ⥤ GrpCat.{u})
      (F : Subfunctor (G ⋙ forget GrpCat))
      (h_sheaf : Presheaf.IsSheaf
        (Scheme.zariskiTopology.over (Spec (CommRingCat.of k))) (G ⋙ forget GrpCat))
      (h_representable : F.toFunctor.IsRepresentable)
      (h_open : ((@IsOpenImmersion).inverseImage
        (Over.forget (Spec (CommRingCat.of k)))).presheaf F.ι)
      (h_fieldPoints : ∀ (K : Type u) [Field K] [Algebra k K]
        (g : G.obj (op (Over.mk (FieldExtension.specMap k K)))),
        ∃ g' : G.obj (op (⊤_ SchemeOverField k)),
          G.map (terminal.from (Over.mk (FieldExtension.specMap k K))).op g' * g ∈
            F.obj (op (Over.mk (FieldExtension.specMap k K)))),
      (yonedaGrp : GroupScheme (Spec (CommRingCat.of k)) ⥤
        (SchemeOverField k)ᵒᵖ ⥤ GrpCat.{u}).essImage G)

end AlgebraicGeometry.GroupScheme
