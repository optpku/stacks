/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CommRingedHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf.LocallyRinged
public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom.Point

/-!
# Local morphisms of small étale ringed sites

A scheme morphism induces a local morphism of its commutative small étale ringed sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSite.Hom
open Scheme.AssociatedModule

noncomputable section

universe u

namespace Scheme.Etale.Small

variable {X Y : Scheme.{u}}

/-- The induced commutative small-étale ringed-site morphism of any scheme morphism is local. -/
instance commRingedHom_isLocal (f : X ⟶ Y) : (commRingedHom f).IsLocal :=
  sorry

end Scheme.Etale.Small
