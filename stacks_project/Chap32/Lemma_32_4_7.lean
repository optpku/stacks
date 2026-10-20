/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.GlobalSections

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 32.4.7 (Tag 01Z0): for a quasi-coherent module `ℱ₀` on a distinguished stage of a
directed inverse system of quasi-compact, quasi-separated schemes with affine transition maps,
the canonical additive-group colimit comparison for global sections of its pullbacks is an
isomorphism. -/
@[stacks 01Z0] #check
  (AlgebraicGeometry.Scheme.Modules.limitPullbackModuleGlobalSectionsColimitMap_isIso :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : OrderDual I, CompactSpace (D.obj j).carrier]
      [∀ j : OrderDual I, QuasiSeparatedSpace (D.obj j).carrier]
      [∀ {j j' : OrderDual I} (f : j ⟶ j'), IsAffineHom (D.map f)]
      (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) [ℱ₀.IsQuasicoherent],
      IsIso
        (AlgebraicGeometry.Scheme.Modules.limitPullbackModuleGlobalSectionsColimitMap
          D c i₀ ℱ₀))
