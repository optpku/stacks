/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import stacks_project.Chap91.Remark_91_4_7_Extension
public import stacks_project.Chap91.Situation_91_3_1_Comparison

/-!
# Canonical infinitesimal and kernel-ideal comparisons for first-order thickenings

The identity infinitesimal comparison of Lemma 91.4.4 is the pushforward-level map whose
restriction is `𝟙 (ℐ ⊗ F)`. A morphism of first-order thickenings supplies the independent
`𝒪_X`-map `f^* 𝒥 ⊗ F ⟶ ℐ ⊗ F` by tensoring `sourceIdealMap` with `F`.
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
  (pullbackPushforwardAdjunction i).homEquiv
    (kernelIdealSheaf i ⊗ (i _*).obj F) K
    ((Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).inv ≫
      tensorHom (𝟙 (idealModule i))
        (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom ≫ φ)

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

/-- The identity infinitesimal comparison `c = 1` of Lemma 91.4.4, as the pushforward-level
map whose restriction is `𝟙 (ℐ ⊗ F)`. -/
noncomputable def identityInfinitesimalMap (F : X.Modules) :
    kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj (idealModule i ⊗ F) :=
  infinitesimalMap_ofRestrict i (𝟙 (idealModule i ⊗ F))

/-- Restricting the identity infinitesimal comparison recovers `𝟙 (ℐ ⊗ F)`. -/
theorem identityInfinitesimalMap_restrict (F : X.Modules) :
    infinitesimalMap_restrict i (identityInfinitesimalMap i F) =
      𝟙 (idealModule i ⊗ F) := sorry

end AlgebraicGeometry.RingedSpace.Modules

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]

/-- The canonical `𝒪_X`-map `f^* 𝒥 ⊗ F ⟶ ℐ ⊗ F` along a morphism of first-order
thickenings, obtained by tensoring `sourceIdealMap` with `F`. -/
def sourceIdealTensorMap (g : T ⟶ U) (F : T.left.Modules) :
    (g.left ^*).obj (RingedSpace.Hom.idealModule U.hom) ⊗ F ⟶
      RingedSpace.Hom.idealModule T.hom ⊗ F :=
  tensorHom (sourceIdealMap g) (𝟙 F)

/-- `sourceIdealTensorMap` is the tensor morphism of `sourceIdealMap` with `𝟙 F`. -/
theorem sourceIdealTensorMap_eq (g : T ⟶ U) (F : T.left.Modules) :
    sourceIdealTensorMap g F = tensorHom (sourceIdealMap g) (𝟙 F) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
