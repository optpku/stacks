module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.K0.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.K0.Pushforward

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure
open DerivedCategory.Bounded.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsProper f]

/-- The derived pushforward of a coherent module is bounded when the target is
quasi-compact. -/
theorem derivedPushforward_isBounded [CompactSpace Y]
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (t.bounded : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace))
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) := sorry

/-- The bounded derived pushforward of a coherent module has coherent cohomology. -/
theorem derivedPushforward_hasCoherentCohomology [CompactSpace Y]
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
      ⟨(RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj),
        derivedPushforward_isBounded f F⟩ := sorry

/-- The bounded coherent object representing `Rf_* F` on a quasi-compact target. -/
noncomputable def derivedPushforward [CompactSpace Y]
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    DerivedCategory.Bounded.CohomologyIn
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) :=
  ⟨⟨(RingedSpace.moduleDerivedPushforward f.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj),
      derivedPushforward_isBounded f F⟩,
    derivedPushforward_hasCoherentCohomology f F⟩

/-- On a quasi-compact target, proper pushforward is the canonical Euler alternating
sum of the classes of all higher direct images. -/
theorem pushforward_of_eq_alternatingSum [CompactSpace Y]
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    pushforward f
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F) =
      fromAbelianK0 Y
        (K0.Euler.value
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)
          (derivedPushforward f F)) := sorry

/-- On a quasi-compact target, the proper-pushforward class of a coherent module is
the Euler class of its bounded derived pushforward. -/
theorem pushforward_of_eq_derived [CompactSpace Y]
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    derivedK0Equiv Y
        (pushforward f
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F)) =
      TriangulatedK0.of (derivedPushforward f F) := sorry

end AlgebraicGeometry.Scheme.K0'
