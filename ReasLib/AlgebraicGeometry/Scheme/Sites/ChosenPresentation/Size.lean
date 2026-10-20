/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.Countable.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Size
public import ReasLib.SetTheory.Cardinal.Bound

/-!
# Size closure of chosen big scheme sites

Size closure ensures that bounded-size schemes and countable coproducts of
represented schemes are represented in the chosen carrier.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ChosenBigSite

variable {P : Precoverage Scheme.{u}}

/-- A chosen big site is size closed if it represents every scheme within the
countable-successor size bound of any represented scheme and represents the
scheme coproduct of every countable family of carrier objects. -/
def IsSizeClosed (𝒮 : ChosenBigSite.{u, v} P) : Prop :=
  (∀ (A : 𝒮.carrier) (T : Scheme.{u}),
    T.size ≤ Cardinal.countableSuccBound (𝒮.toScheme.obj A).size →
      ∃ B : 𝒮.carrier, Nonempty (𝒮.toScheme.obj B ≅ T)) ∧
  (∀ (ι : Type (max u v)) [Countable ι] (A : ι → 𝒮.carrier),
    ∃ (U : 𝒮.carrier) (c : Cofan fun i ↦ 𝒮.toScheme.obj (A i))
      (_ : IsColimit c), Nonempty (𝒮.toScheme.obj U ≅ c.pt))

namespace IsSizeClosed

/-- Size closure is equivalent to bounded-size representation and representation
of countable scheme coproducts. -/
theorem iff (𝒮 : ChosenBigSite.{u, v} P) :
    IsSizeClosed 𝒮 ↔
      (∀ (A : 𝒮.carrier) (T : Scheme.{u}),
        T.size ≤ Cardinal.countableSuccBound (𝒮.toScheme.obj A).size →
          ∃ B : 𝒮.carrier, Nonempty (𝒮.toScheme.obj B ≅ T)) ∧
      (∀ (ι : Type (max u v)) [Countable ι] (A : ι → 𝒮.carrier),
        ∃ (U : 𝒮.carrier) (c : Cofan fun i ↦ 𝒮.toScheme.obj (A i))
          (_ : IsColimit c), Nonempty (𝒮.toScheme.obj U ≅ c.pt)) :=
  Iff.rfl

/-- Every scheme within the countable-successor size bound of a represented
scheme is isomorphic to a scheme represented by the carrier. -/
theorem exists_iso_of_size_le_bound {𝒮 : ChosenBigSite.{u, v} P}
    (h : IsSizeClosed 𝒮) (A : 𝒮.carrier) (T : Scheme.{u})
    (hT : T.size ≤ Cardinal.countableSuccBound (𝒮.toScheme.obj A).size) :
    ∃ B : 𝒮.carrier, Nonempty (𝒮.toScheme.obj B ≅ T) :=
  h.1 A T hT

/-- A countable family of carrier objects has a scheme coproduct isomorphic to
a scheme represented by the carrier. -/
theorem exists_countable_coproduct {𝒮 : ChosenBigSite.{u, v} P}
    (h : IsSizeClosed 𝒮) {ι : Type (max u v)} [Countable ι]
    (A : ι → 𝒮.carrier) :
    ∃ (U : 𝒮.carrier) (c : Cofan fun i ↦ 𝒮.toScheme.obj (A i))
      (_ : IsColimit c), Nonempty (𝒮.toScheme.obj U ≅ c.pt) :=
  h.2 ι A

end IsSizeClosed

end AlgebraicGeometry.ChosenBigSite
