module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage

/-!
Compatibility import for the canonical small-étale sheaf adjunction and its
unit/counit specifications.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

#check (AlgebraicGeometry.AlgebraicSpace.sheafAdjunction :
  ∀ {S : Scheme.{u}} (A : Type v) [Category.{w} A]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ A,
      (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P]
    [∀ F : (smallEtaleSite Y)ᵒᵖ ⥤ A, (etaleBaseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology X) A],
    sheafInverseImage A f ⊣ sheafPushforward A f)
