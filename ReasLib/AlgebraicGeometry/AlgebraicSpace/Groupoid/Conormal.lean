/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InfinitesimalSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Conormal action of infinitesimal source sections

An infinitesimal source section of a groupoid with flat source and target acts
as the identity on the conormal sheaf of an invariant first-order thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace
open Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
variable {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
variable [IsFirstOrderThickening ι] (δ : InfinitesimalSection G ι)

/-- The target endomorphism of an infinitesimal source section is `t ∘ δ`. -/
def InfinitesimalSection.target : G.U.left ⟶ G.U.left :=
  (δ.arrow ≫ G.t).left

/-- The target endomorphism is the underlying morphism of the section followed by the target. -/
theorem InfinitesimalSection.target_eq :
    InfinitesimalSection.target G ι δ = (δ.arrow ≫ G.t).left :=
  rfl

/-- The target endomorphism of an infinitesimal source section restricts to the
identity on the first-order thickening. -/
theorem InfinitesimalSection.targetCommSq :
    CommSq (𝟙 U₀) ι ι (InfinitesimalSection.target G ι δ) :=
  sorry

/-- The conormal endomorphism induced by the target of an infinitesimal source
section, using the identity-pullback comparison. -/
def InfinitesimalSection.conormalMap :
    conormalSheaf ι ⟶ conormalSheaf ι :=
  (SmallEtaleModuleGlueing.modulesPullbackId U₀).inv.app
      (conormalSheaf ι) ≫
    Conormal.map (InfinitesimalSection.targetCommSq G ι δ)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- The conormal endomorphism is the inverse identity-pullback comparison followed
by the canonical conormal map of the target square. -/
theorem InfinitesimalSection.conormalMap_eq :
    (InfinitesimalSection.conormalMap G ι δ : conormalSheaf ι ⟶ conormalSheaf ι) =
      ((SmallEtaleModuleGlueing.modulesPullbackId U₀).inv.app
          (conormalSheaf ι) ≫
        Conormal.map (InfinitesimalSection.targetCommSq G ι δ) :
          conormalSheaf ι ⟶ conormalSheaf ι) :=
  rfl

/-- For a groupoid with flat source and target, an infinitesimal source section
along an invariant first-order thickening induces the identity on its conormal sheaf. -/
theorem InfinitesimalSection.conormalMap_eq_id
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    (h_invariant : CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι)) :
    InfinitesimalSection.conormalMap G ι δ =
      𝟙 (conormalSheaf ι) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
