module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/- Lemma 59.29.7: the site-point stalk functor associated to the canonical small-étale point is
the geometric étale stalk. -/
@[stacks 04FM] #check (AlgebraicGeometry.Scheme.Etale.pointSmallEtale_stalk :
    ∀ {S : Scheme.{u}} (s : Scheme.GeometricPoint S)
      (F : S.Etaleᵒᵖ ⥤ Type u),
      (@Scheme.pointSmallEtale S s.K inferInstance
        (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom).presheafFiber.obj F =
        Scheme.Etale.stalk s F)

end AlgebraicGeometry.Scheme.GeometricPoint
