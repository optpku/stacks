/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.CohomologyDuality

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ExceptionalInverseImage

/- Lemma 48.22.5: for a proper scheme over a local Noetherian ring whose dimension is
the sum of the closed-fibre dimension and the base dimension, the dualizing module on the
scheme represents `F ↦ Hom_A(H^d(X, F), ωA)` on coherent modules. -/
@[stacks 0AWP] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.representsCohomologyDual :
    {A : Type u} → [CommRing A] → [IsLocalRing A] → [IsNoetherianRing A] → {X : Scheme.{u}} →
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] →
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)] →
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) →
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) →
      (ωA : DerivedCategory (ModuleCat.{u} A)) →
      (hωA : ωA.IsNormalizedDualizingComplex HA) →
      (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace) →
      (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA)) →
      (f : X ⟶ Spec (CommRingCat.of A)) → [IsProper f] →
      (fShriek : Scheme.ExceptionalInverseImage f) → (d n : ℕ) →
      topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) = d →
      topologicalKrullDim X = n →
      topologicalKrullDim X = (d : WithBot ℕ∞) + ringKrullDim A →
      (ωX : X.Modules) →
      (hωX : RingedSpace.ModuleDerived.IsDualizingModule
        (fShriek.functor.obj ωS)
        HX
        (-(n : ℤ))
        ωX) →
      Nonempty ((Scheme.Hom.cohomologyDualFunctor f d
        (DerivedCategory.IsNormalizedDualizingComplex.dualizingModule HA ωA hωA)).RepresentableBy
          hωX.toCoh))

end AlgebraicGeometry.Scheme.ExceptionalInverseImage
