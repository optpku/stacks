/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Immersion
public import ReasLib.RingTheory.LocalRing.TameSymbol.Determinant

/-!
# Prime divisors and reduced point closures

This file records dimension, residue-field, restricted-section, and tame-symbol constructions
for the reduced closure of the generic point of a prime divisor.
-/

@[expose] public section

open CategoryTheory Function Set Topology
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace PrimeDivisor

/-- The relative dimension of the generic point of a prime divisor is one less than the
relative dimension of the generic point of its integral ambient scheme. -/
theorem relativeDimensionFunction_genericPoint_eq
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
    (Z : PrimeDivisor X) :
    p.relativeDimensionFunction δ Z.genericPoint = (n - 2) + 1 := sorry

/-- The reduced point closure of a prime divisor has relative dimension one less than the
relative dimension of the integral ambient scheme. -/
theorem pointClosure_relativeDimension
    {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] [IsIntegral X] (n : ℤ)
    (hX : p.relativeDimensionFunction δ (_root_.genericPoint X) = n)
    (Z : PrimeDivisor X) :
    (Scheme.PointClosure.ι Z.genericPoint ≫ p).relativeDimensionFunction δ
        (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint)) =
      (n - 2) + 1 := sorry

/-- A locally finite family of prime-divisor supports gives a locally finite family of their
reduced point closures. -/
theorem pointClosuresLocallyFinite {X : Scheme.{u}} [IsIntegral X]
    {I : Type v} (Z : I → PrimeDivisor X)
    (hlocal : LocallyFinite fun i ↦ ((Z i).support : Set X)) :
    LocallyFinite fun i ↦
      (Scheme.PointClosure.closedSubset (Z i).genericPoint : Set X) := sorry

/-- The local ring at the generic point of a prime divisor has Krull dimension one. -/
theorem ringKrullDim_genericPointStalk {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (Z : PrimeDivisor X) :
    ringKrullDim Z.genericPointStalk = 1 := sorry

/-- The canonical map from the residue field at a prime divisor's generic point to the
function field of its reduced point closure. -/
noncomputable def residueToPointClosureFunctionField {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (Z : PrimeDivisor X) :
    IsLocalRing.ResidueField Z.genericPointStalk →+*
      (Scheme.PointClosure.scheme Z.genericPoint).functionField :=
  IsLocalRing.ResidueField.lift
    (((X.presheaf.stalkCongr
      (.of_eq (Scheme.PointClosure.ι_map_genericPoint Z.genericPoint).symm)).hom ≫
        (Scheme.PointClosure.ι Z.genericPoint).stalkMap
          (_root_.genericPoint
            (Scheme.PointClosure.scheme Z.genericPoint))).hom)

/-- The residue-to-point-closure map agrees with the transported stalk map after taking a
residue. -/
theorem residueToPointClosureFunctionField_residue {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (Z : PrimeDivisor X)
    (a : Z.genericPointStalk) :
    residueToPointClosureFunctionField Z (IsLocalRing.residue _ a) =
      ((X.presheaf.stalkCongr
        (.of_eq (Scheme.PointClosure.ι_map_genericPoint Z.genericPoint).symm)).hom ≫
          (Scheme.PointClosure.ι Z.genericPoint).stalkMap
            (_root_.genericPoint
              (Scheme.PointClosure.scheme Z.genericPoint))) a := sorry

end PrimeDivisor

namespace Scheme.RegularMeromorphicSectionOrderPresentation

/-- The chosen stalk generator in a local order presentation, pulled back to the generic stalk
of the reduced closure of the prime divisor. -/
noncomputable def generatorOnPointClosure {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X]
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {Z : PrimeDivisor X} (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    RingedSpace.stalkModuleCat
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ)
      (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint)) :=
  @RingedSpace.Hom.pullbackStalkUnitHom
    (Scheme.PointClosure.scheme Z.genericPoint).toRingedSpace X.toRingedSpace
    (Scheme.PointClosure.ι Z.genericPoint).toLRSHom.toShHom ℒ
    (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint))
    ((Scheme.PointClosure.ι_map_genericPoint Z.genericPoint).symm ▸ data.generator)

/-- The pulled-back generator is the image of the chosen presentation generator under the
canonical pullback map on stalks. -/
theorem generatorOnPointClosure_def {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X]
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {Z : PrimeDivisor X} (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    generatorOnPointClosure data =
      @RingedSpace.Hom.pullbackStalkUnitHom
        (Scheme.PointClosure.scheme Z.genericPoint).toRingedSpace X.toRingedSpace
        (Scheme.PointClosure.ι Z.genericPoint).toLRSHom.toShHom ℒ
        (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint))
        ((Scheme.PointClosure.ι_map_genericPoint Z.genericPoint).symm ▸
          data.generator) := sorry

/-- The meromorphic section on the reduced point closure induced by the chosen generator in a
local order presentation. -/
noncomputable def restrictToPointClosure {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X]
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {Z : PrimeDivisor X} (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    (Scheme.PointClosure.scheme Z.genericPoint).toLocallyRingedSpace.meromorphicSections
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ) :=
  Function.invFun
    (fun section_ ↦ SheafOfModules.sectionGermOfCommRing section_
      (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint)))
    ((Scheme.PointClosure.scheme Z.genericPoint).toLocallyRingedSpace.meromorphicSectionStalkMap
      ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ)
      (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint))
      (generatorOnPointClosure data))

/-- The generic germ of the restricted generator is its canonical image in the meromorphic
stalk. -/
theorem restrictToPointClosure_genericGerm {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X]
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {Z : PrimeDivisor X} (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    SheafOfModules.sectionGermOfCommRing (restrictToPointClosure data)
        (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint)) =
      (Scheme.PointClosure.scheme Z.genericPoint).toLocallyRingedSpace.meromorphicSectionStalkMap
        ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ)
        (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint))
        (generatorOnPointClosure data) := sorry

/-- A meromorphic section with the prescribed generic germ is the restricted section, so the
construction is independent of the choice made by `Function.invFun`. -/
theorem restrictToPointClosure_unique {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X]
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {Z : PrimeDivisor X} (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z)
    (section_ :
      (Scheme.PointClosure.scheme Z.genericPoint).toLocallyRingedSpace.meromorphicSections
        ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ))
    (hsection : SheafOfModules.sectionGermOfCommRing section_
        (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint)) =
      (Scheme.PointClosure.scheme Z.genericPoint).toLocallyRingedSpace.meromorphicSectionStalkMap
        ((Scheme.Modules.pullback (Scheme.PointClosure.ι Z.genericPoint)).obj ℒ)
        (_root_.genericPoint (Scheme.PointClosure.scheme Z.genericPoint))
        (generatorOnPointClosure data)) :
    section_ = restrictToPointClosure data := sorry

/-- The meromorphic section induced by a stalk generator on the reduced point closure is
nonzero. -/
theorem restrictToPointClosure_ne_zero {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X]
    {ℒ : X.Modules} [Modules.Invertible ℒ]
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s}
    {Z : PrimeDivisor X} (data : RegularMeromorphicSectionOrderPresentation ℒ s hs Z) :
    restrictToPointClosure data ≠ 0 := sorry

end Scheme.RegularMeromorphicSectionOrderPresentation

namespace PrimeDivisor

/-- The tame symbol of two local presentation quotients, transported to the function field of
the reduced point closure. -/
noncomputable def tameSymbolOnPointClosure {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (Z : PrimeDivisor X)
    (f g : (FractionRing Z.genericPointStalk)ˣ) :
    (Scheme.PointClosure.scheme Z.genericPoint).functionFieldˣ :=
  Units.map (residueToPointClosureFunctionField Z).toMonoidHom
    (TameSymbol.value Z.genericPointStalk (FractionRing Z.genericPointStalk)
      (ringKrullDim_genericPointStalk Z) f g)

/-- The point-closure tame symbol is the image of the local tame symbol under the canonical
residue-to-function-field map. -/
theorem tameSymbolOnPointClosure_def {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsIntegral X] (Z : PrimeDivisor X)
    (f g : (FractionRing Z.genericPointStalk)ˣ) :
    tameSymbolOnPointClosure Z f g =
      Units.map (residueToPointClosureFunctionField Z).toMonoidHom
        (TameSymbol.value Z.genericPointStalk (FractionRing Z.genericPointStalk)
          (ringKrullDim_genericPointStalk Z) f g) := sorry

end PrimeDivisor

end AlgebraicGeometry
