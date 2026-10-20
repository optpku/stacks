/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Composition.Open

/-!
# Ranges of morphisms of groupoid schemes

This module records closure properties of the arrow-image of a morphism of groupoid schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- The arrow-image of an identity-on-objects morphism contains every identity arrow of the
target groupoid. -/
lemma rangeArrow_mem_identity {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    {hU : G₁.U = G₂.U} (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) (u : G₂.U.left) :
    G₂.e.left u ∈ Set.range f.arrow.left := by
  let u₁ : G₁.U.left := (Over.Hom.left (eqToHom hU.symm)) u
  refine ⟨G₁.e.left u₁, ?_⟩
  have hObj : f.obj = eqToHom hU := by
    simpa [IsIdentityOnObjects] using hf
  have hMapE :
      G₁.e.left ≫ f.arrow.left =
        Over.Hom.left (eqToHom hU) ≫ G₂.e.left := by
    simpa [hObj, Category.assoc] using congrArg Over.Hom.left (Hom.map_e f)
  have hEval :
      f.arrow.left (G₁.e.left u₁) =
        G₂.e.left ((Over.Hom.left (eqToHom hU)) u₁) := by
    exact congrArg (fun g : G₁.U.left ⟶ G₂.R.left => g u₁) hMapE
  have hu₁ : (Over.Hom.left (eqToHom hU)) u₁ = u := by
    change (Over.Hom.left (eqToHom hU.symm ≫ eqToHom hU)) u = u
    simpa using
      congrArg (fun g : G₂.U.left ⟶ G₂.U.left => g u)
        (congrArg Over.Hom.left (eqToHom_trans hU.symm hU))
  calc
    f.arrow.left (G₁.e.left u₁) =
      G₂.e.left ((Over.Hom.left (eqToHom hU)) u₁) := hEval
    _ = G₂.e.left u := by rw [hu₁]

/-- The arrow-image of a groupoid-scheme morphism is stable under inverse. -/
lemma rangeArrow_mem_inverse {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (f : Hom G₁ G₂) {r : G₂.R.left} (hr : r ∈ Set.range f.arrow.left) :
    G₂.i.left r ∈ Set.range f.arrow.left := by
  rcases hr with ⟨r₁, rfl⟩
  refine ⟨G₁.i.left r₁, ?_⟩
  have hMapI : G₁.i.left ≫ f.arrow.left = f.arrow.left ≫ G₂.i.left := by
    simpa [Category.assoc] using congrArg Over.Hom.left (Hom.map_i f)
  exact congrArg (fun g : G₁.R.left ⟶ G₂.R.left => g r₁) hMapI

/-- The arrow-image of an identity-on-objects morphism is stable under composition. -/
lemma rangeArrow_mem_comp {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    {hU : G₁.U = G₂.U} (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    (z : (Limits.pullback G₂.s G₂.t).left)
    (hz_fst : (Limits.pullback.fst G₂.s G₂.t).left z ∈ Set.range f.arrow.left)
    (hz_snd : (Limits.pullback.snd G₂.s G₂.t).left z ∈ Set.range f.arrow.left) :
    G₂.c.left z ∈ Set.range f.arrow.left := sorry

/-- For an identity-on-objects morphism of groupoid schemes over a field spectrum, an open
arrow-image is closed. -/
theorem isClosed_range_of_isOpen {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    (h_open : IsOpen (Set.range f.arrow.left)) :
    IsClosed (Set.range f.arrow.left) := sorry

end AlgebraicGeometry.GroupoidScheme.Hom
