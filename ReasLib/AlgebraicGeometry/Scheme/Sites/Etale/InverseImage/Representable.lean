module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.SheafifiedRepresentable

universe u w

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology (Type (max w (u + 1)))]
variable [HasWeakSheafify Y.smallEtaleTopology (Type (max w (u + 1)))]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type (max w (u + 1)),
  (smallEtalePullback f).op.HasLeftKanExtension P]

/-- Inverse image of a sheafified representable on the small étale site is the
sheafified representable of its base change. -/
noncomputable def smallEtaleInverseImage_representableIso (V : Y.Etale) :
    ((smallEtalePullback f).sheafPullback (Type (max w (u + 1)))
      Y.smallEtaleTopology X.smallEtaleTopology).obj
        (Y.smallEtaleTopology.uliftSheafifiedRepresentable.{max w (u + 1), u, u + 1} V) ≅
      X.smallEtaleTopology.uliftSheafifiedRepresentable.{max w (u + 1), u, u + 1}
        ((smallEtalePullback f).obj V) :=
  (pullbackIso (smallEtalePullback f) Y.smallEtaleTopology X.smallEtaleTopology V).symm

/-- The forward representable comparison is the inverse of the canonical
sheafified-representable pullback comparison. -/
theorem smallEtaleInverseImage_representableIso_hom (V : Y.Etale) :
    (smallEtaleInverseImage_representableIso f V).hom =
      (pullbackIso (smallEtalePullback f) Y.smallEtaleTopology
        X.smallEtaleTopology V).inv := sorry

end AlgebraicGeometry.Scheme
