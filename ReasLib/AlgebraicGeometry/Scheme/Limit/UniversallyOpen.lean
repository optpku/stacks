/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.Affine

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Limit
namespace QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- If the limit base change of a locally finitely presented morphism is locally
quasi-finite and universally open, then both properties hold at one common stage
above the distinguished stage. -/
theorem exists_locallyQuasiFinite_universallyOpen_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_lqf : LocallyQuasiFinite s.limitHom) (h_open : UniversallyOpen s.limitHom)
    (h_fp : LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      LocallyQuasiFinite (s.stageHom i hi0i) ∧ UniversallyOpen (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange
end Limit
end Scheme
end AlgebraicGeometry
