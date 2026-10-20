/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Galois
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Galois
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Galois descent for Picard groups

Picard pullback along a Galois field extension identifies line-bundle classes over the base
with the classes fixed by the canonical Galois action after base change.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.FieldExtension

/-- If a quasi-compact and quasi-separated `k`-scheme `X` has
`k ≃ Γ(X, 𝒪_X)` and a `k`-rational point, then pullback along any Galois extension
`K/k` bijects `X.PicardGroup` with the Galois-fixed Picard classes after base change. -/
@[stacks 0CDT]
theorem picardPullback_bijOn_fixedPoints
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : SchemeOverField k) [CompactSpace X.left.carrier]
    [QuasiSeparatedSpace X.left.carrier]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_point : Nonempty (𝟙_ (SchemeOverField k) ⟶ X)) :
    Set.BijOn (Scheme.Hom.picardPullback (FieldExtension.toSource k K X.hom)) Set.univ
      (Picard.galoisFixedSubgroup k K X.hom : Set _) := sorry

end AlgebraicGeometry.FieldExtension
