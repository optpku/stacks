module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Abelian

/-!
# Abelian inverse image along pro-étale relocalization

The abelian sheaf functor induced by small-to-big pro-étale relocalization and
its computation formulas.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

#check (AlgebraicGeometry.Scheme.ProEt.iInverseImage f :
    Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_eq f :
    iInverseImage f =
      (SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (topology T) (proetaleTopology.over S))

#check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_obj_obj f :
    ∀ (F : Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) (U : T.ProEt),
      ((iInverseImage f).obj F).1.obj (Opposite.op U) =
        F.1.obj (Opposite.op ((SmallToBig.relocalizationFunctor f).obj U)))

end AlgebraicGeometry.Scheme.ProEt

