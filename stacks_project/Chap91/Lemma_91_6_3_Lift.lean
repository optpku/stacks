/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import stacks_project.Chap91.Lemma_91_5_6_Lift
public import stacks_project.Chap91.Situation_91_6_2_Diagram

/-!
# Flat lifts of `π^* F` and `h^* F'_2`

In Situation 91.6.2, the inverse images `π^* F` and `h^* F'_2` are `𝒪'_1`-modules
flat over `S'_1` whose inverse image along `i1` recovers `F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening.Hom (FlatLift)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- First-order thickenings are preserved by the bundled `Thickening.of` constructor. -/
theorem isFirstOrderThickening_ofHom {Y Y' : RingedSpace.{u}}
    (i : Y ⟶ Y') [IsFirstOrderThickening i] :
    IsFirstOrderThickening (Thickening.of i).hom := sorry

/-- Transport `IsFirstOrderThickening` along the bundled `Thickening.of` constructor. -/
instance instIsFirstOrderThickening_ofHom {Y Y' : RingedSpace.{u}}
    (i : Y ⟶ Y') [IsFirstOrderThickening i] :
    IsFirstOrderThickening (Thickening.of i).hom :=
  isFirstOrderThickening_ofHom i

namespace IsFirstOrderThickening
namespace SesFlatThickenings

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}

/-- Inverse image along `Thickening.of i` agrees with inverse image along `i`. -/
noncomputable def thickeningOf_pullbackIso {Y Y' : RingedSpace.{u}}
    (i : Y ⟶ Y') [IsThickening i] (M : Y'.Modules) :
    ((Thickening.of i).hom ^*).obj M ≅ (i ^*).obj M :=
  eqToIso (congrArg (fun (φ : Y ⟶ Y') ↦ (φ ^*).obj M) (Thickening.of_hom i))

/-- `thickeningOf_pullbackIso` is the pullback of `Thickening.of_hom`. -/
theorem thickeningOf_pullbackIso_eq {Y Y' : RingedSpace.{u}}
    (i : Y ⟶ Y') [IsThickening i] (M : Y'.Modules) :
    thickeningOf_pullbackIso i M =
      eqToIso (congrArg (fun (φ : Y ⟶ Y') ↦ (φ ^*).obj M) (Thickening.of_hom i)) := sorry

variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
variable [IsFirstOrderThickening t2] [IsFirstOrderThickening t3]

/-- Bundled flat lifts of the restriction `F` along `(f, f'_1)`. -/
abbrev sourceFlatLift (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  @FlatLift (Thickening.of i1) (Thickening.of t1)
    (isFirstOrderThickening_ofHom i1) (isFirstOrderThickening_ofHom t1) g F

/-- Bundled flat lifts of the restriction `F` along `(f, f'_2)`. -/
abbrev middleFlatLift (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  let g := thickeningHom2 σ
  let F := moduleRestrict σ
  @FlatLift (Thickening.of i2) (Thickening.of t2)
    (isFirstOrderThickening_ofHom i2) (isFirstOrderThickening_ofHom t2) g F

/-- The morphism `f'_1` is flat. -/
instance instIsFlat_f1' (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    RingedSpace.Hom.IsFlat σ.f1' :=
  σ.flat1

/-- The morphism `f'_3` is flat. -/
instance instIsFlat_f3' (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    RingedSpace.Hom.IsFlat σ.f3' :=
  σ.flat3

/-- The restriction `F = F'_2|_X` is flat over `S`. -/
instance instIsFlatOver_moduleRestrict (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (moduleRestrict σ) f := sorry

/-- The inverse image `π^* F` is flat over `S'_1`. -/
instance instIsFlatOver_splitPullback
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (((canonicalSplitting σ) ^*).obj (moduleRestrict σ)) σ.f1' :=
  sorry

/-- The inverse image `h^* F'_2` is flat over `S'_1`. -/
instance instIsFlatOver_homPullback (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver ((σ.h.hom ^*).obj σ.module) σ.f1' := sorry

/-- The stored module `F'_2` as a flat lift of `F` along `(f, f'_2)`. -/
noncomputable def moduleLift (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    middleFlatLift σ :=
  let g := thickeningHom2 σ
  let F := moduleRestrict σ
  @FlatLift.of (Thickening.of i2) (Thickening.of t2)
    (isFirstOrderThickening_ofHom i2) (isFirstOrderThickening_ofHom t2)
    g F σ.module (thickeningOf_pullbackIso i2 σ.module) σ.module_isFlatOver

/-- The middle module of `moduleLift` is the stored `𝒪'_2`-module. -/
theorem moduleLift_module (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (moduleLift σ).module = σ.module := sorry

/-- Inverse image of `F'_2` along the bundled thickening recovers `F`. -/
def moduleLift_sourceRestrict (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  (moduleLift σ).restrictIso

/-- The inverse image `π^* F` of the restriction `F = F'_2|_X`, as a flat lift along
`(f, f'_1)`. -/
noncomputable def splitPullback
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    sourceFlatLift σ :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  let F' := ((canonicalSplitting σ) ^*).obj F
  @FlatLift.of (Thickening.of i1) (Thickening.of t1)
    (isFirstOrderThickening_ofHom i1) (isFirstOrderThickening_ofHom t1) g F F'
    (thickeningOf_pullbackIso i1 F' ≪≫
      (pullbackCompIso i1 (canonicalSplitting σ)).symm.app F ≪≫
      eqToIso (congrArg (fun (φ : X ⟶ X) ↦ (φ ^*).obj F)
        (canonicalSplitting_leftInv σ)) ≪≫
      (pullbackIdIso X).app F)
    (instIsFlatOver_splitPullback σ)

/-- The middle module of `splitPullback` is `π^* F`. -/
theorem splitPullback_module
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (splitPullback σ).module = ((canonicalSplitting σ) ^*).obj (moduleRestrict σ) := sorry

/-- Inverse image of `π^* F` along `i1` recovers `F`. -/
theorem splitPullback_restrictIso
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Nonempty ((i1 ^*).obj (splitPullback σ).module ≅ moduleRestrict σ) := sorry

/-- Inverse image of `π^* F` along the bundled thickening recovers `F`. -/
def splitPullback_sourceRestrict
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  (splitPullback σ).restrictIso

/-- The inverse image `h^* F'_2`, as a flat lift along `(f, f'_1)`. -/
noncomputable def homPullback (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    sourceFlatLift σ :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  let F' := (σ.h.hom ^*).obj σ.module
  @FlatLift.of (Thickening.of i1) (Thickening.of t1)
    (isFirstOrderThickening_ofHom i1) (isFirstOrderThickening_ofHom t1) g F F'
    (thickeningOf_pullbackIso i1 F' ≪≫
      (pullbackCompIso i1 σ.h.hom).symm.app σ.module ≪≫
      eqToIso (congrArg (fun (φ : X ⟶ X2) ↦ (φ ^*).obj σ.module) σ.h.w))
    (instIsFlatOver_homPullback σ)

/-- The middle module of `homPullback` is `h^* F'_2`. -/
theorem homPullback_module (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (homPullback σ).module = (σ.h.hom ^*).obj σ.module := sorry

/-- Inverse image of `h^* F'_2` along `i1` recovers `F`. -/
theorem homPullback_restrictIso (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Nonempty ((i1 ^*).obj (homPullback σ).module ≅ moduleRestrict σ) := sorry

/-- Inverse image of `h^* F'_2` along the bundled thickening recovers `F`. -/
def homPullback_sourceRestrict (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  (homPullback σ).restrictIso

end SesFlatThickenings
end IsFirstOrderThickening
end AlgebraicGeometry.RingedSpace
