/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangles of pseudo-coherent derived module sheaves

For a fixed degree, pseudo-coherence has the shifted two-out-of-three property expected from
strict-perfect approximations.  The object property and its shift API are named here so downstream
developments do not have to rebuild local approximation or rotation arguments.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The object property of being `m`-pseudo-coherent on a ringed site. -/
abbrev mPseudoCoherent (m : ℤ) : ObjectProperty (ModuleDerived.{w} X) :=
  fun K => K.IsMPseudoCoherent m

namespace IsMPseudoCoherent

/-- Pseudo-coherence in a fixed degree is invariant under isomorphism. -/
theorem ofIso {K L : ModuleDerived.{w} X} (e : K ≅ L) {m : ℤ}
    (hK : K.IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := sorry

/-- Shifting by `n` translates the pseudo-coherence bound by `n`. -/
theorem shift_iff (K : ModuleDerived.{w} X) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := sorry

/-- Lemma 21.45.4 (1): the third vertex of a distinguished triangle inherits the indicated
pseudo-coherence bound. -/
@[stacks 08FV "(1)"]
theorem obj₃ {m : ℤ} (T : Triangle (ModuleDerived.{w} X))
    (hT : T ∈ distTriang (ModuleDerived.{w} X))
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := sorry

/-- Lemma 21.45.4 (2): the middle vertex of a distinguished triangle inherits the common
pseudo-coherence bound. -/
@[stacks 08FV "(2)"]
theorem obj₂ {m : ℤ} (T : Triangle (ModuleDerived.{w} X))
    (hT : T ∈ distTriang (ModuleDerived.{w} X))
    (h₁ : T.obj₁.IsMPseudoCoherent m)
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := sorry

/-- Lemma 21.45.4 (3): the first vertex of a distinguished triangle inherits the shifted
pseudo-coherence bound. -/
@[stacks 08FV "(3)"]
theorem obj₁ {m : ℤ} (T : Triangle (ModuleDerived.{w} X))
    (hT : T ∈ distTriang (ModuleDerived.{w} X))
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := sorry

end IsMPseudoCoherent

/-- Fixed-degree pseudo-coherence satisfies the two-out-of-three property for distinguished
triangles. -/
instance mPseudoCoherent_isTriangulatedClosed₂ (m : ℤ) :
    ObjectProperty.IsTriangulatedClosed₂ (mPseudoCoherent (X := X) m) := sorry

/-- Fixed-degree pseudo-coherence is invariant under isomorphism. -/
instance mPseudoCoherent_isClosedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms (mPseudoCoherent (X := X) m) := sorry

end RingedSite.Hom.ModuleDerived
