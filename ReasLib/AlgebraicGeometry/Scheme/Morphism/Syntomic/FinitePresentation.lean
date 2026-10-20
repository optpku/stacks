/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

/-!
# Finite-presentation consequences of syntomicity

Syntomic scheme morphisms are locally of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Syntomic

/-- A syntomic morphism of schemes is locally of finite presentation. -/
theorem locallyOfFinitePresentation (hf : Syntomic f) :
    LocallyOfFinitePresentation f := by
  rw [Scheme.Hom.locallyOfFinitePresentation_iff_locallyOfType f]
  refine ⟨fun x ↦ ?_⟩
  rcases (LocallyOfType.exists_affineNeighborhood RingHom.Syntomic hf x) with
    ⟨U, hxU, V, e, hsyntomic⟩
  exact ⟨U, hxU, V, e, RingHom.Syntomic.finitePresentation hsyntomic⟩

end Syntomic

/-- Syntomic morphisms canonically infer as locally of finite presentation. -/
instance instLocallyOfFinitePresentationOfSyntomic [hf : Syntomic f] :
    LocallyOfFinitePresentation f :=
  Syntomic.locallyOfFinitePresentation hf

end AlgebraicGeometry
