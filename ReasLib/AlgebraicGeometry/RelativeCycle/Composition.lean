/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition

/-!
# Composition of relative cycles

Composition of fibre-cycle families preserves the relative-cycle condition and
induces a bilinear map on the additive groups of relative cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Composition of a family of `r`-cycles on fibres of `X ⟶ Y` with a family of
`e`-cycles on fibres of `Y ⟶ S`, as a family of `(r + e)`-cycles on fibres of
`X ⟶ S`. -/
noncomputable def comp {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e) : (f ≫ p).FiberCycleFamily (r + e : ℕ) :=
  FiberCycleFamily.reindex (Int.natCast_add r e).symm (CyclesOnFibers.comp α β)

/-- Unfolding `comp` recovers reindexing of `CyclesOnFibers.comp` from degree
`(r : ℤ) + e` to `(r + e : ℤ)`. -/
theorem comp_def {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e) :
    comp α β =
      FiberCycleFamily.reindex (Int.natCast_add r e).symm
        (CyclesOnFibers.comp α β) := Eq.refl (comp α β)

private theorem comp_zero_right {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α : f.FiberCycleFamily r) : comp α (0 : p.FiberCycleFamily e) = 0 := by
  rw [comp_def, CyclesOnFibers.comp_zero_right, FiberCycleFamily.reindex_zero]

private theorem comp_zero_left {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (β : p.FiberCycleFamily e) : comp (0 : f.FiberCycleFamily r) β = 0 := by
  rw [comp_def, CyclesOnFibers.comp_zero_left, FiberCycleFamily.reindex_zero]

private theorem comp_add_right {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α : f.FiberCycleFamily r) (β₁ β₂ : p.FiberCycleFamily e) :
    comp α (β₁ + β₂) = comp α β₁ + comp α β₂ := by
  simp only [comp_def, CyclesOnFibers.comp_add_right, FiberCycleFamily.reindex_add]

private theorem comp_add_left {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α₁ α₂ : f.FiberCycleFamily r) (β : p.FiberCycleFamily e) :
    comp (α₁ + α₂) β = comp α₁ β + comp α₂ β := by
  simp only [comp_def, CyclesOnFibers.comp_add_left, FiberCycleFamily.reindex_add]

/-- If `α` is a relative `r`-cycle on `X / Y` and `β` is a
relative `e`-cycle on `Y / S`, with `S` locally Noetherian and `X ⟶ Y ⟶ S`
locally of finite type, then the composite family `comp α β` is a relative
`(r + e)`-cycle on `X / S`. -/
theorem isRelative_comp {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e) (hα : IsRelative α) (hβ : IsRelative β) :
    IsRelative (comp α β) := sorry

/-- The composite of relative cycles lies in `z(X/S, r + e)`. -/
theorem comp_mem_group {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e) (hα : IsRelative α) (hβ : IsRelative β) :
    comp α β ∈ group (f ≫ p) (r + e) :=
  (mem_group_iff (f ≫ p) (r + e) (comp α β)).mpr (isRelative_comp p f α β hα hβ)

/-- The bilinear composition map
`z(X/Y, r) →+ z(Y/S, e) →+ z(X/S, r + e)`. -/
noncomputable def groupComp {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] (r e : ℕ) :
    group f r →+ group p e →+ group (f ≫ p) (r + e) :=
  let make {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
      (c : A → B → C) (hzero_right : ∀ a, c a 0 = 0)
      (hzero_left : ∀ b, c 0 b = 0)
      (hadd_right : ∀ a b₁ b₂, c a (b₁ + b₂) = c a b₁ + c a b₂)
      (hadd_left : ∀ a₁ a₂ b, c (a₁ + a₂) b = c a₁ b + c a₂ b)
      (HA : AddSubgroup A) (HB : AddSubgroup B) (HC : AddSubgroup C)
      (hc : ∀ (a : HA) (b : HB), c a b ∈ HC) : HA →+ HB →+ HC :=
    { toFun := fun a ↦
        { toFun := fun b ↦ ⟨c a b, hc a b⟩
          map_zero' := Subtype.ext (hzero_right a)
          map_add' := fun b₁ b₂ ↦ Subtype.ext (hadd_right a b₁ b₂) }
      map_zero' := AddMonoidHom.ext fun b ↦ Subtype.ext (hzero_left b)
      map_add' := fun a₁ a₂ ↦ AddMonoidHom.ext fun b ↦
        Subtype.ext (hadd_left a₁ a₂ b) }
  make comp
    (by intro α; exact comp_zero_right α)
    (by intro β; exact comp_zero_left β)
    (by intro α β₁ β₂; exact comp_add_right α β₁ β₂)
    (by intro α₁ α₂ β; exact comp_add_left α₁ α₂ β)
    (group f r) (group p e) (group (f ≫ p) (r + e))
    (fun α β ↦ comp_mem_group p f (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e)
      α.property β.property)

/-- The underlying fibrewise family of `groupComp` is family-level `comp`. -/
theorem groupComp_apply {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [IsLocallyNoetherian S] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℕ}
    (α : group f r) (β : group p e) :
    (groupComp p f r e α β : (f ≫ p).FiberCycleFamily (r + e : ℕ)) =
      comp (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e) :=
  Eq.refl (comp (α : f.FiberCycleFamily r) (β : p.FiberCycleFamily e))


end AlgebraicGeometry.RelativeCycle
