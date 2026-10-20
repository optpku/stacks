/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.ResiduePredeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt

/-! # Versality of formal objects over schemes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The identity object of the slice of `Spec(A)` as a complete local object. -/
def CompleteLocalObject.identity (A : CompleteLocalSAlgebra S) :
    CompleteLocalObject (slice (Over.mk A.toS)) :=
  CompleteLocalObject.of A (sliceIdentityObject A.toS)
    (sliceIdentityObject_over A.toS)

/-- The identity complete local object has base `A`. -/
theorem CompleteLocalObject.identity_base (A : CompleteLocalSAlgebra S) :
    (CompleteLocalObject.identity A).base = A := rfl

/-- The identity complete local object is the identity slice object over
`Spec(A)`. -/
theorem CompleteLocalObject.identity_spec (A : CompleteLocalSAlgebra S) :
    (CompleteLocalObject.identity A).object = sliceIdentityObject A.toS ∧
      (slice (Over.mk A.toS)).p.obj (CompleteLocalObject.identity A).object =
        Over.mk A.toS := ⟨rfl, sliceIdentityObject_over A.toS⟩

namespace FormalObject

/-- The identity formal object of the slice of `Spec(A)`, obtained by
restricting the identity slice object along all truncations. -/
def identity (A : CompleteLocalSAlgebra S) :
    FormalObject (slice (Over.mk A.toS)) :=
  restriction (CompleteLocalObject.identity A)

/-- The identity formal object has complete local base `A`. -/
theorem identity_base (A : CompleteLocalSAlgebra S) :
    (identity A).base = A := rfl

/-- The identity formal object is the truncation system of the identity slice
object of `Spec(A)`. -/
theorem identity_spec (A : CompleteLocalSAlgebra S) :
    (identity A).base = A ∧
      (identity A).stageOne =
        restrictionObj (CompleteLocalObject.identity A) 0 := ⟨rfl, rfl⟩


/-- The residue-predeformation projection of a scheme-level formal object is
cofibered in groupoids. -/
instance instIsFiberedInGroupoidsOp_toPredeformation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (ξ : FormalObject X) {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
          openImmersion =
        ξ.base.toS) :
    Functor.IsFibered.InGroupoids
      (predeformationProjection ξ openImmersion h_toS).op :=
  sorry

/-- A scheme-level formal object is versal when, after every affine-open
factorization of `Spec(R) ⟶ S`, the associated formal object of
`ℱ_{X, κ(R), ξ₁}` is versal. -/
def IsVersalOnObjects {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) : Prop :=
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
          openImmersion =
        ξ.base.toS),
    _root_.FormalObject.IsVersal (toPredeformation ξ openImmersion h_toS)

/-- Versality of a scheme-level formal object is formal versality of
`toPredeformation` on every affine-open factorization. -/
theorem isVersalOnObjects_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) :
    IsVersalOnObjects ξ ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ ξ.base.carrier]
        [Module.Finite Λ (ResidueField ξ.base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_toS :
          Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
              openImmersion =
            ξ.base.toS),
        _root_.FormalObject.IsVersal (toPredeformation ξ openImmersion h_toS) :=
  sorry

/-- A formal object is versal if its canonical residue-predeformation object is versal
for every affine-open factorization of its complete local base. -/
class IsVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) : Prop where
  /-- Versality in the canonical residue-predeformation category. -/
  isVersalOnObjects : IsVersalOnObjects ξ

namespace IsVersal

/-- Versality gives a versal canonical predeformation object over every affine open. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) [IsVersal ξ]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier] [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_toS : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
      openImmersion = ξ.base.toS) :
    _root_.FormalObject.IsVersal (toPredeformation ξ openImmersion h_toS) :=
  IsVersal.isVersalOnObjects openImmersion h_toS

/-- Scheme-level versality is canonical residue-predeformation versality. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) :
    IsVersal ξ ↔ IsVersalOnObjects ξ :=
  ⟨fun h => h.isVersalOnObjects, fun h => ⟨h⟩⟩

end IsVersal

/-- The identity formal object of a complete local spectrum is versal. -/
instance instIsVersal_identity {S : Scheme.{u}} [IsLocallyNoetherian S]
    (A : CompleteLocalSAlgebra S) : IsVersal (identity A) := sorry

end FormalObject

end AlgebraicGeometry.GroupoidsOver
