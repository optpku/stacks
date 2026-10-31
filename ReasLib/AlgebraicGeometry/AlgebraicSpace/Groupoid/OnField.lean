/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Groupoids in algebraic spaces on a field

A groupoid in algebraic spaces over `B` is on a field when its object space is
`Spec(k)` for a field `k` over the base scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The object space of a groupoid in algebraic spaces is the spectrum of a field over `S`. -/
class IsOnField {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) where
  /-- An identification of the object space with `Spec (.of k)` over `S`. -/
  objectSpaceIsoData : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)

namespace IsOnField

def objectSpaceIso {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [h : IsOnField G σ] :
    G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ) := h.objectSpaceIsoData

/-- An isomorphism with the field spectrum makes a groupoid on that field over `S`. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (h : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) : IsOnField G σ := ⟨h⟩

end IsOnField

/-- Being on a field is equivalent to having a nonempty identification with `Spec (.of k)` over `S`. -/
theorem isOnField_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) :
    Nonempty (IsOnField G σ) ↔ Nonempty (G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.objectSpaceIsoData⟩
  · rintro ⟨e⟩
    exact ⟨⟨e⟩⟩

/-- The discrete groupoid on `Spec (.of k)` over `B` is on the field `k`. -/
instance instIsOnField_discrete {S : Scheme.{u}} {B : AlgebraicSpace S} {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) (p : AlgebraicSpace.ofOver (Over.mk σ) ⟶ B) :
    IsOnField (discrete (Over.mk p)) σ := ⟨Iso.refl _⟩

end AlgebraicGeometry.GroupoidAlgebraicSpace
