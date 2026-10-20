/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.DerivedTensor
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.34.3: if derived global sections of `E ⊗ᴸ K` are pseudo-coherent over
the base ring for every perfect `E`, then they are pseudo-coherent for every
pseudo-coherent `E`. -/
@[stacks 0CSH] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalSectionsTensor_mapsToPseudoCoherent :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
      (K : Scheme.ModuleDerived.Quasicoherent X),
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj →
        (RingedSpace.ModuleDerived.perfect ≤
          ObjectProperty.inverseImage DerivedCategory.IsPseudoCoherent
            (Right.functor K.obj ⋙
              Modules.Kunneth.globalSectionsOver f ⋙
                ModuleCat.derivedRestrictionOfScalars
                  (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) →
          (fun E : RingedSpace.ModuleDerived X.toRingedSpace ↦
            RingedSpace.ModuleDerived.IsPseudoCoherent E) ≤
              ObjectProperty.inverseImage DerivedCategory.IsPseudoCoherent
                (Right.functor K.obj ⋙
                  Modules.Kunneth.globalSectionsOver f ⋙
                    ModuleCat.derivedRestrictionOfScalars
                      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))

end AlgebraicGeometry.Scheme.DerivedQCoh
