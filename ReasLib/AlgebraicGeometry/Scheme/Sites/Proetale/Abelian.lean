module

public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.SmallToBig
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

/-!
# Abelian inverse image along pro-étale relocalization

Inverse image from the big pro-étale site to a small pro-étale site is
computed by precomposition with the relocalization functor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Inverse image on abelian sheaves along pro-étale relocalization from the big
site over `S` to the small pro-étale site of `T`. -/
abbrev iInverseImage :
    Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T) AddCommGrpCat.{u + 1} :=
  (SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (topology T) (proetaleTopology.over S)

/-- Inverse image on abelian sheaves is continuous sheaf pushforward along
pro-étale relocalization. -/
theorem iInverseImage_eq :
    iInverseImage f =
      (SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (topology T) (proetaleTopology.over S) := rfl

/-- Inverse image of an abelian sheaf evaluates on the same scheme viewed over
`S`. -/
theorem iInverseImage_obj_obj
    (F : Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) (U : T.ProEt) :
    ((iInverseImage f).obj F).1.obj (Opposite.op U) =
      F.1.obj (Opposite.op ((SmallToBig.relocalizationFunctor f).obj U)) := rfl

/-- Inverse image on abelian sheaves along small pro-étale base change `f_small`. -/
abbrev smallInverseImage
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T) AddCommGrpCat.{u + 1} :=
  (smallProetalePullback f).sheafPullback AddCommGrpCat.{u + 1}
    (topology S) (topology T)

/-- Inverse image `f_small⁻¹` is sheaf pullback along `smallProetalePullback`. -/
theorem smallInverseImage_eq
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    smallInverseImage f =
      (smallProetalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        (topology S) (topology T) := rfl

/-- Inverse image `f_small⁻¹` on abelian sheaves preserves finite limits. -/
instance smallInverseImage_preservesFiniteLimits
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits (smallInverseImage f) := sorry

/-- Inverse image `f_small⁻¹` on abelian sheaves preserves finite colimits. -/
instance smallInverseImage_preservesFiniteColimits
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteColimits (smallInverseImage f) := sorry

/-- Inverse image `iInverseImage f` on abelian sheaves preserves finite limits. -/
instance iInverseImage_preservesFiniteLimits
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    PreservesFiniteLimits (iInverseImage f) := sorry

/-- Inverse image `iInverseImage f` on abelian sheaves preserves finite colimits. -/
instance iInverseImage_preservesFiniteColimits
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits (iInverseImage f) := sorry


end AlgebraicGeometry.Scheme.ProEt
