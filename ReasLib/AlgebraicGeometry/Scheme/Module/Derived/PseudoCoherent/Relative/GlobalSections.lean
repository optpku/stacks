module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.GlobalSections
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BoundednessDetection
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Derived.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- If a scheme is separated and of finite presentation over an affine base and the derived
global sections of `E ⊗ᴸ K` are pseudo-coherent for every pseudo-coherent `E`, then `K` is
pseudo-coherent relative to the base. -/
theorem isPseudoCoherentOver_of_globalSectionsTensor
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] (K : DerivedQCoh X) :
    (∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPseudoCoherent E →
        DerivedCategory.IsPseudoCoherent
          ((Scheme.FlatPullbackSections.baseSections f).obj (E ⊗ᴸ K.obj))) →
      Scheme.ModuleDerived.IsPseudoCoherentOver f K.obj := sorry

/-- If a scheme is separated and of finite presentation over an affine base and the derived
global sections of `E ⊗ᴸ K` are pseudo-coherent for every perfect `E`, then `K` is
pseudo-coherent relative to the base. -/
theorem isPseudoCoherentOver_of_globalSectionsTensor_perfect
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [Scheme.Hom.FinitePresentation f] (K : DerivedQCoh X)
    (hperfect : ∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.IsPseudoCoherent
          ((Scheme.FlatPullbackSections.baseSections f).obj (E ⊗ᴸ K.obj))) :
    Scheme.ModuleDerived.IsPseudoCoherentOver f K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
