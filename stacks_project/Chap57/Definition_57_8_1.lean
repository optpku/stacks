/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Category
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 57.8.1: The Fourier--Mukai functor with kernel `K` is the composite of
derived pullback to `X ×ₛ Y`, derived tensor product with `K`, and derived pushforward to `Y`.
Its restrictions to preserved subcategories are also called Fourier--Mukai functors. -/
@[stacks 0FYQ] #check
  (AlgebraicGeometry.Scheme.FourierMukai.functor :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
      (K : AlgebraicGeometry.RingedSpace.ModuleDerived
        (CategoryTheory.Limits.pullback f g).toRingedSpace),
      AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace ⥤
        AlgebraicGeometry.RingedSpace.ModuleDerived Y.toRingedSpace)

section

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)

/- The unrestricted restriction API applies to quasicoherent complexes. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.restrict
  (P := Scheme.ModuleDerived.quasicoherentProperty X)
  (Q := Scheme.ModuleDerived.quasicoherentProperty Y) f g K :
  Scheme.ModuleDerived.quasicoherentProperty X ≤
    (Scheme.ModuleDerived.quasicoherentProperty Y).inverseImage
      (Scheme.FourierMukai.functor f g K) →
    (Scheme.ModuleDerived.quasicoherentProperty X).FullSubcategory ⥤
      (Scheme.ModuleDerived.quasicoherentProperty Y).FullSubcategory)

/- The unrestricted restriction API applies to perfect complexes. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.restrict
  (P := RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace))
  (Q := RingedSpace.ModuleDerived.perfect (X := Y.toRingedSpace)) f g K :
  RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace) ≤
    (RingedSpace.ModuleDerived.perfect (X := Y.toRingedSpace)).inverseImage
      (Scheme.FourierMukai.functor f g K) →
    (RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace)).FullSubcategory ⥤
      (RingedSpace.ModuleDerived.perfect (X := Y.toRingedSpace)).FullSubcategory)

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

/- The unrestricted restriction API applies to coherent complexes. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.restrict
  (P := DerivedCategory.cohomologyIn
    (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf))
  (Q := DerivedCategory.cohomologyIn
    (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)) f g K :
  DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ≤
    (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)).inverseImage
      (Scheme.FourierMukai.functor f g K) →
    (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)).FullSubcategory)

/- The unrestricted restriction API applies to bounded coherent complexes. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.restrict
  (P := DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).bounded)
  (Q := DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).bounded) f g K :
  (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).bounded) ≤
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
      (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).bounded).inverseImage
      (Scheme.FourierMukai.functor f g K) →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).bounded).FullSubcategory ⥤
      (DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
        (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).bounded).FullSubcategory)

/- The unrestricted restriction API applies to bounded-below coherent complexes. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.restrict
  (P := DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).plus)
  (Q := DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).plus) f g K :
  (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).plus) ≤
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
      (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).plus).inverseImage
      (Scheme.FourierMukai.functor f g K) →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).plus).FullSubcategory ⥤
      (DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
        (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).plus).FullSubcategory)

/- The unrestricted restriction API applies to bounded-above coherent complexes. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.restrict
  (P := DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).minus)
  (Q := DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).minus) f g K :
  (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
    (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).minus) ≤
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
      (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).minus).inverseImage
      (Scheme.FourierMukai.functor f g K) →
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⊓
      (DerivedCategory.TStructure.t (C := X.toRingedSpace.Modules)).minus).FullSubcategory ⥤
      (DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf) ⊓
        (DerivedCategory.TStructure.t (C := Y.toRingedSpace.Modules)).minus).FullSubcategory)

end
