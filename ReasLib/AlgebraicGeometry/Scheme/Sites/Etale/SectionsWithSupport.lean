module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Z : Scheme.{u}}

/-- Direct image on small étale abelian sheaves is exact for a closed immersion. -/
theorem directImage_exact_of_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology) := sorry

/-- Direct image along a closed immersion preserves injective abelian sheaves on the small
étale sites. -/
instance directImage_preservesInjectiveObjects (i : Z ⟶ X) [IsClosedImmersion i] :
    ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology Z.smallEtaleTopology).PreservesInjectiveObjects := sorry

/-- The sheaf of sections on `X` supported on the image of a closed immersion. -/
noncomputable def sectionsWithSupportOn (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  kernel ((abelianAdjunction (closedImmersionComplement i).ι).unit)

/-- The canonical inclusion of sections with support into the ambient sheaf. -/
noncomputable def sectionsWithSupportOnι (i : Z ⟶ X) [IsClosedImmersion i] :
    sectionsWithSupportOn i ⟶ 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  kernel.ι ((abelianAdjunction (closedImmersionComplement i).ι).unit)

/-- The sheaf of sections with support on a closed subscheme, viewed on that subscheme. -/
noncomputable def sectionsWithSupport (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} :=
  sectionsWithSupportOn i ⋙ abelianInverseImage i

/-- A section lies in the supported subsheaf exactly when it vanishes on the complementary open. -/
theorem mem_range_sectionsWithSupportOnι_iff (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : X.Etale)
    (σ : F.1.obj (op U)) :
    σ ∈ Set.range
        ((((sectionsWithSupportOnι i).app F).hom.app (op U)) :
          ((sectionsWithSupportOn i).obj F).1.obj (op U) → F.1.obj (op U)) ↔
      (let W : U.left.Opens := TopologicalSpace.Opens.comap U.hom.base.hom
          (closedImmersionComplement (S := X) i)
       F.1.map (MorphismProperty.Over.homMk W.ι :
         (Scheme.Etale.mk (W.ι ≫ U.hom) : X.Etale) ⟶ U).op σ = 0) := sorry

/-- The supported subsheaf is recovered from its realization on the closed subscheme. -/
instance sectionsWithSupportOn_unit_isIso (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((abelianAdjunction i).unit.app ((sectionsWithSupportOn i).obj F)) := sorry

/-- Sections with support on a closed immersion preserve injective abelian sheaves. -/
instance sectionsWithSupport_injective (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective F] :
    Injective ((sectionsWithSupport i).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale
