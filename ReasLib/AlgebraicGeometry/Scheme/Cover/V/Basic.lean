/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily
public import ReasLib.RingTheory.Valuation.Extension

/-!
# Valuative chart covers

This module adds the valuative lifting condition to the topology-independent
finite affine-family data owned by `Scheme.Cover.AffineFamily`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

namespace AffineFamilyOver

variable {T : Scheme.{u}}

/-- A finite affine family over an affine target is a standard `V` cover when every
valuation-ring point of the target lifts through one of its charts after an extension of
valuation rings. -/
@[stacks 0ETB]
def IsStandardVCover (family : AffineFamilyOver T) : Prop :=
  IsAffine T ∧
    ∀ ⦃V : Type u⦄ [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (CommRingCat.of V) ⟶ T),
        ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
          (_ : Algebra V W) (_ : IsExtensionOfValuationRings V W)
          (j : Fin family.n) (lift : Spec (CommRingCat.of W) ⟶ family.U j),
            Spec.map (CommRingCat.ofHom (algebraMap V W)) ≫ g = lift ≫ family.map j

/-- A finite affine family is a standard `V` cover exactly when its target is affine and every
valuation-ring point lifts through one of its charts after extending the valuation ring. -/
theorem isStandardVCover_iff_valuativeLift (family : AffineFamilyOver T) :
    IsStandardVCover family ↔
      IsAffine T ∧
        ∀ ⦃V : Type u⦄ [CommRing V] [IsDomain V] [ValuationRing V]
          (g : Spec (CommRingCat.of V) ⟶ T),
            ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
              (_ : Algebra V W) (_ : IsExtensionOfValuationRings V W)
              (j : Fin family.n) (lift : Spec (CommRingCat.of W) ⟶ family.U j),
                Spec.map (CommRingCat.ofHom (algebraMap V W)) ≫ g =
                  lift ≫ family.map j := sorry

/-- A standard `V` cover provides a valuative factorization after extending
the valuation ring. -/
theorem IsStandardVCover.exists_valuativeLift
    {family : AffineFamilyOver T} (h : IsStandardVCover family)
    {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    (g : Spec (CommRingCat.of V) ⟶ T) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
      (_ : Algebra V W) (_ : IsExtensionOfValuationRings V W)
      (j : Fin family.n) (lift : Spec (CommRingCat.of W) ⟶ family.U j),
        Spec.map (CommRingCat.ofHom (algebraMap V W)) ≫ g = lift ≫ family.map j := sorry

end AffineFamilyOver

end

end AlgebraicGeometry
