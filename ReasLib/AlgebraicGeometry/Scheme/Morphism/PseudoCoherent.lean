/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic

/-!
# Pseudo-coherent morphisms of schemes

A scheme morphism is pseudo-coherent when its maps on compatible affine coordinate rings are
pseudo-coherent ring maps.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A scheme morphism is pseudo-coherent when every induced map on compatible affine
coordinate rings is a pseudo-coherent ring map. -/
@[mk_iff]
class PseudoCoherent (f : X ⟶ Y) : Prop where
  /-- The induced ring map on compatible affine opens is pseudo-coherent. -/
  pseudoCoherent_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsPseudoCoherentRingMap

namespace PseudoCoherent

/-- Scheme-level pseudo-coherence is associated with pseudo-coherence of ring maps. -/
instance instHasRingHomProperty :
    HasRingHomProperty (@PseudoCoherent.{u}) RingHom.IsPseudoCoherentRingMap := sorry

/-- A morphism between affine spectra is pseudo-coherent exactly when its defining ring map is
pseudo-coherent. -/
lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PseudoCoherent (Spec.map f) ↔ f.hom.IsPseudoCoherentRingMap := sorry

end PseudoCoherent

end AlgebraicGeometry
