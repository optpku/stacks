/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.K0

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsProper f]

/-- The coherent higher direct image in degree `i`, regarded as an object of the
coherent full subcategory on the target. -/
noncomputable def higherDirectImage
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory)
    (i : ℕ) :
    (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory :=
  ⟨RingedSpace.Hom.higherDirectImageModule f.toShHom F.obj i,
    @higherDirectImageModule_isCoherent_of_proper X Y f _ _ F.obj F.property i⟩

/-- The direct sum of the even higher direct images of a coherent module is coherent. -/
theorem evenHigherDirectImages_isCoherent
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (∐ fun i : ℕ ↦
      RingedSpace.Hom.higherDirectImageModule f.toShHom F.obj (2 * i)).IsCoherent := sorry

/-- The direct sum of the odd higher direct images of a coherent module is coherent. -/
theorem oddHigherDirectImages_isCoherent
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (∐ fun i : ℕ ↦
      RingedSpace.Hom.higherDirectImageModule f.toShHom F.obj (2 * i + 1)).IsCoherent := sorry

/-- The coherent direct sum of the even higher direct images. -/
noncomputable def evenHigherDirectImages
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory :=
  ⟨∐ fun i : ℕ ↦ RingedSpace.Hom.higherDirectImageModule f.toShHom F.obj (2 * i),
    evenHigherDirectImages_isCoherent f F⟩

/-- The coherent direct sum of the odd higher direct images. -/
noncomputable def oddHigherDirectImages
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).FullSubcategory :=
  ⟨∐ fun i : ℕ ↦ RingedSpace.Hom.higherDirectImageModule f.toShHom F.obj (2 * i + 1),
    oddHigherDirectImages_isCoherent f F⟩

/-- The Euler value assigned to a coherent module by proper pushforward. -/
noncomputable def pushforwardValue
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) : K0' Y :=
  ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
      (evenHigherDirectImages f F) -
    ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
      (oddHigherDirectImages f F)

/-- Long exact sequences of higher direct images make `pushforwardValue` additive on
short exact sequences of coherent modules. -/
theorem relations_le_ker_pushforwardValue :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ≤
      (FreeAbelianGroup.lift (pushforwardValue f)).ker := sorry

/-- The additive proper-pushforward map on coherent Grothendieck groups. -/
noncomputable def pushforward : K0' X →+ K0' Y :=
  ObjectProperty.GrothendieckGroup.lift
    (pushforwardValue f) (relations_le_ker_pushforwardValue f)

/-- Proper pushforward sends a coherent module to the difference between the classes
of the direct sums of its even and odd higher direct images. -/
theorem pushforward_of
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    pushforward f
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F) =
      ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
          (evenHigherDirectImages f F) -
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
          (oddHigherDirectImages f F) := sorry

end AlgebraicGeometry.Scheme.K0'
