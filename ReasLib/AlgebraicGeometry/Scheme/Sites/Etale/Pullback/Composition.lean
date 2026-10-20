module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The inverse-image comparison for a composite of morphisms of schemes. -/
noncomputable def smallEtaleSheafPullbackCompIso
    {A : Type v} [Category.{w} A]
    [HasWeakSheafify X.smallEtaleTopology A]
    [HasWeakSheafify Y.smallEtaleTopology A]
    [HasWeakSheafify Z.smallEtaleTopology A]
    [∀ P : Y.Etaleᵒᵖ ⥤ A, (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ P : Z.Etaleᵒᵖ ⥤ A, (smallEtalePullback g).op.HasLeftKanExtension P]
    [∀ P : Z.Etaleᵒᵖ ⥤ A, (smallEtalePullback (f ≫ g)).op.HasLeftKanExtension P] :
    (smallEtalePullback (f ≫ g)).sheafPullback A Z.smallEtaleTopology X.smallEtaleTopology ≅
      (smallEtalePullback g).sheafPullback A Z.smallEtaleTopology Y.smallEtaleTopology ⋙
        (smallEtalePullback f).sheafPullback A Y.smallEtaleTopology X.smallEtaleTopology := by
  exact (Adjunction.leftAdjointCompIso
    (smallEtalePullback_sheafAdjunction g A)
    (smallEtalePullback_sheafAdjunction f A)
    (smallEtalePullback_sheafAdjunction (f ≫ g) A)
    (let siteIso :
        smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g) :=
     (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm
     Functor.sheafPushforwardContinuousComp' siteIso A Z.smallEtaleTopology
       Y.smallEtaleTopology X.smallEtaleTopology)).symm

end AlgebraicGeometry.Scheme
