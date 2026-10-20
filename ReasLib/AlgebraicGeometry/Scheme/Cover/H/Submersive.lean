/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Submersive
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Universal submersiveness and h covering families

This module characterizes finite h covering families of finite type over a
Noetherian scheme by universal submersiveness of their coproduct morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- For a finite family of finite type morphisms to a Noetherian scheme, the
coproduct morphism is universally submersive exactly when the family is an h
covering. -/
theorem universallySubmersive_sigmaDesc_iff_hCovering
    {X : Scheme.{u}} {ι : Type u} [Finite ι] [IsNoetherian X]
    (family : ι → Over X) [∀ i, Scheme.Hom.FiniteType (family i).hom] :
    UniversallySubmersive (Limits.Sigma.desc (fun i ↦ (family i).hom)) ↔
      HCovering family := sorry

end AlgebraicGeometry.Scheme
