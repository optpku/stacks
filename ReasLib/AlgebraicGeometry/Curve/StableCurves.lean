/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Stable
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

/-!
# Stable families of algebraic-space curves

Stability is the stable-curve property of every field-valued fibre, expressed
using its representing scheme and the induced structure map to the field.
The genus-`g` locus additionally requires `R¹ f_* 𝒪` to be finite locally free of rank `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme over the field represented by a scheme presentation of a field-valued fibre. -/
def ofFibreScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (p : FieldValuedPoint Y) (T : Over S) (e : pullback f p.hom ≅ ofOver T) :
    SchemeOverField p.K :=
  Over.mk
    (yonedaEquiv
      (e.inv ≫ pullback.snd f p.hom : yoneda.obj T ⟶ yoneda.obj p.overObj)).left

namespace Spaces.Curves

/-- The object property of curve families whose field-valued fibres are stable curves. -/
def stable (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ ∀ p : FieldValuedPoint (ofOver (base P)),
    ∃ (T : Over S) (e : pullback (hom P) p.hom ≅ ofOver T),
      isStableCurve (ofFibreScheme p T e)

/-- A stable curve family of genus `g` has `R¹ f_* 𝒪` finite locally free of rank `g`. -/
def stableOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ stable S P ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in the genus-`g` stable locus is stability together with the rank condition. -/
theorem stableOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    stableOfGenus g S P ↔ stable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P)) :=
  Iff.rfl

/-- The genus-`g` stable locus is contained in the stable locus. -/
theorem stableOfGenus_le_stable (g : ℕ) (S : Scheme.{u}) :
    stableOfGenus g S ≤ stable S :=
  sorry

/-- Over a nonempty base, the genus of a stable family of curves is unique. -/
theorem eq_of_mem_stableOfGenus {S : Scheme.{u}} {P : Obj S}
    [Nonempty (base P).left] {g g' : ℕ}
    (hg : stableOfGenus g S P) (hg' : stableOfGenus g' S P) : g = g' :=
  sorry

/-- The genus-`g` stable locus is closed under isomorphisms of curve families. -/
instance instIsClosedUnderIsomorphisms_stableOfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (stableOfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

end Spaces.Curves

end AlgebraicGeometry.AlgebraicSpace
