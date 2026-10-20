/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes.Qcqs
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.DerivedTensor
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- If derived global sections of `E ⊗ᴸ K` are pseudo-coherent over the base ring for
every perfect derived module `E`, then they are pseudo-coherent for every pseudo-coherent
derived module `E`. -/
theorem globalSectionsTensor_mapsToPseudoCoherent
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Scheme.ModuleDerived.Quasicoherent X)
    (hK_boundedAbove :
      (t.minus :
        ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
    (hperfect :
      RingedSpace.ModuleDerived.perfect ≤
        ObjectProperty.inverseImage DerivedCategory.IsPseudoCoherent
          (Right.functor K.obj ⋙
            Modules.Kunneth.globalSectionsOver f ⋙
              ModuleCat.derivedRestrictionOfScalars
                (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    (fun E : RingedSpace.ModuleDerived X.toRingedSpace ↦
      RingedSpace.ModuleDerived.IsPseudoCoherent E) ≤
        ObjectProperty.inverseImage DerivedCategory.IsPseudoCoherent
          (Right.functor K.obj ⋙
            Modules.Kunneth.globalSectionsOver f ⋙
              ModuleCat.derivedRestrictionOfScalars
                (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
