/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Proper

/-!
# Proper support in inverse limits of schemes

This file concerns finite-stage descent of proper scheme-theoretic support for
modules pulled back through a directed inverse system of schemes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange

/-- If the scheme-theoretic support of the limit pullback of a finite-type
quasicoherent module is proper over the limit target, then its scheme-theoretic
support is proper over the target at some finite stage. -/
theorem exists_isProper_schemeTheoreticSupport_stage_of_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (F0 : X0.Modules) [F0.IsQuasicoherent] [F0.IsFiniteType]
    (h_limit : IsProper
      ((Scheme.Modules.schemeTheoreticSupport
        (Scheme.Modules.baseChangeModule s.hom
          (pullback.fst s.targetMap (s.limitCone.cone.π.app i0)) F0)).subschemeι ≫
        s.limitHom))
    (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsProper
      ((Scheme.Modules.schemeTheoreticSupport
        (Scheme.Modules.baseChangeModule s.hom
          (pullback.fst s.targetMap (D.map (homOfLE hi0i))) F0)).subschemeι ≫
        s.stageHom i hi0i) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
