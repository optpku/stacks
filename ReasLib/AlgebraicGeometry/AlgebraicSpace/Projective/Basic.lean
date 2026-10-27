/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveAtlas

/-! # Projective morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is projective when it admits a closed-immersion
presentation in the projective atlas of a finite-type quasi-coherent module on its
target. -/
class Projective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- A finite-type quasi-coherent projective-atlas presentation of `f`. -/
  exists_presentation :
    ∃ (E : Y.Modules) (hE : E.IsQuasicoherent) (hFT : E.IsFiniteType)
      (i : X ⟶ @ProjectiveAtlas.space S Y E hE),
      IsClosedImmersion i ∧ i ≫ @ProjectiveAtlas.projection S Y E hE = f

/-- Projectivity is equivalent to the existence of a closed immersion into a projective
atlas of a finite-type quasi-coherent module whose composite is the given morphism. -/
theorem projective_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Projective f ↔
      ∃ (E : Y.Modules) (hE : E.IsQuasicoherent) (hFT : E.IsFiniteType)
        (i : X ⟶ @ProjectiveAtlas.space S Y E hE),
        IsClosedImmersion i ∧ i ≫ @ProjectiveAtlas.projection S Y E hE = f :=
  sorry

/-- The structure projection of a projective atlas of a finite-type quasi-coherent
module is projective. -/
instance instProjective_projection {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : X.Modules) [E.IsQuasicoherent] [E.IsFiniteType] :
    Projective (ProjectiveAtlas.projection E) where
  exists_presentation :=
    ⟨E, inferInstance, inferInstance, 𝟙 _, inferInstance,
      Category.id_comp (ProjectiveAtlas.projection E)⟩

end AlgebraicGeometry.AlgebraicSpace
