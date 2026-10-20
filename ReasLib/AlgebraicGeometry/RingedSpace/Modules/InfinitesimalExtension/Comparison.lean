module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Obstruction

/-!
# Intrinsic and pushforward infinitesimal comparisons

Inverse restriction identifies intrinsic ideal-action maps with pushforward comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]

/-- The pushforward-level infinitesimal comparison attached to an `𝒪_X`-map
`φ : ℐ ⊗ F ⟶ K`, obtained by inverting `infinitesimalMap_restrict` via the
pullback-pushforward adjunction, the monoidal comparison of pullback, and the counit
isomorphism on `F`. -/
noncomputable def infinitesimalMap_ofRestrict {F K : X.Modules}
    (φ : idealModule i ⊗ F ⟶ K) :
    kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K :=
  (infinitesimalComparisonEquiv i F K).symm φ

/-- `infinitesimalMap_ofRestrict` is the adjunction transpose of the composite of `μIso.inv`,
the counit of `F`, and the given `𝒪_X`-map. -/
theorem infinitesimalMap_ofRestrict_eq {F K : X.Modules}
    (φ : idealModule i ⊗ F ⟶ K) :
    infinitesimalMap_ofRestrict i φ =
      (pullbackPushforwardAdjunction i).homEquiv
        (kernelIdealSheaf i ⊗ (i _*).obj F) K
        ((Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).inv ≫
          tensorHom (𝟙 (idealModule i))
            (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom ≫ φ) := sorry

/-- Restricting the pushforward-level comparison recovers the original `𝒪_X`-map. -/
theorem infinitesimalMap_restrict_ofRestrict {F K : X.Modules}
    (φ : idealModule i ⊗ F ⟶ K) :
    infinitesimalMap_restrict i (infinitesimalMap_ofRestrict i φ) = φ := sorry

/-- The pushforward comparison corresponding to the identity on the ideal tensor module. -/
noncomputable def identityInfinitesimalMap (F : X.Modules) :
    kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj (idealModule i ⊗ F) :=
  infinitesimalMap_ofRestrict i (𝟙 (idealModule i ⊗ F))

/-- Restricting the identity infinitesimal comparison recovers `𝟙 (ℐ ⊗ F)`. -/
theorem identityInfinitesimalMap_restrict (F : X.Modules) :
    infinitesimalMap_restrict i (identityInfinitesimalMap i F) =
      𝟙 (idealModule i ⊗ F) := sorry

end AlgebraicGeometry.RingedSpace.Modules

