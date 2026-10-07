module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Impurity

/- Lemma 38.15.4: under Situation 38.15.1, an impurity above `s` whose base-change
scheme is a directed inverse limit of affine schemes over `S` descends through a cone
projection to an impurity at some finite stage. -/
@[stacks 05IZ] #check
  (AlgebraicGeometry.Scheme.Modules.Impurity.exists_stage :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      [F.IsQuasicoherent] [F.IsFiniteType] (s : S) (J : Impurity F f s)
      {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Over S)
      (π : (Functor.const (OrderDual I)).obj (Over.mk J.g) ⟶ D)
      (hπ : IsLimit (⟨Over.mk J.g, π⟩ : Cone D))
      [∀ i : I, IsAffine (D.obj i).left],
      ∃ i : I, J.DescendsAlong (D.obj i).hom (π.app i).left (π.app i).w)

end Impurity
end Modules
end Scheme
end AlgebraicGeometry
