/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.FreeDimensional.Action
public import ReasLib.AlgebraicGeometry.FreeDimensionalAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.Points
public import Mathlib.CategoryTheory.NatIso

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry
namespace FA

private theorem actionGroupoid_laws (d : ℕ) [NeZero d] :
    (∀ T : Scheme.{u}ᵒᵖ,
      mapAction (d := d) (Scheme.Γ.map (𝟙 T)).hom =
        𝟭 (ActionCategory (glFixOne Γ(T.unop, ⊤) d)ᵐᵒᵖ
          (FreeDimAlgebra Γ(T.unop, ⊤) d))) ∧
    (∀ (T T' T'' : Scheme.{u}ᵒᵖ) (f : T ⟶ T') (g : T' ⟶ T''),
      mapAction (d := d) (Scheme.Γ.map (f ≫ g)).hom =
        mapAction (Scheme.Γ.map f).hom ⋙ mapAction (Scheme.Γ.map g).hom) := sorry

/-- The presheaf of action groupoids of unit-fixing automorphisms. -/
def actionGroupoid (d : ℕ) [NeZero d] : Scheme.{u}ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := Grpd.of (ActionCategory (glFixOne Γ(T.unop, ⊤) d)ᵐᵒᵖ (FreeDimAlgebra Γ(T.unop, ⊤) d))
  map f := mapAction (Scheme.Γ.map f).hom
  map_id := (actionGroupoid_laws d).1
  map_comp := (actionGroupoid_laws d).2 _ _ _

/-- The action-groupoid fibre over a scheme. -/
theorem actionGroupoid_obj (d : ℕ) [NeZero d] (T : Scheme.{u}) :
    (actionGroupoid d).obj (op T) =
      Grpd.of (ActionCategory (glFixOne Γ(T, ⊤) d)ᵐᵒᵖ (FreeDimAlgebra Γ(T, ⊤) d)) := rfl

/-- Restriction of the action-groupoid presheaf along a scheme morphism. -/
theorem actionGroupoid_map (d : ℕ) [NeZero d] {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T') :
    (actionGroupoid d).map f = mapAction (Scheme.Γ.map f).hom := rfl

private theorem fibreIso_laws (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (toAction Γ(T.unop, ⊤) d ⋙ fromAction Γ(T.unop, ⊤) d =
      𝟭 (FreeDimAlgebra Γ(T.unop, ⊤) d)) ∧
    (fromAction Γ(T.unop, ⊤) d ⋙ toAction Γ(T.unop, ⊤) d =
      𝟭 (ActionCategory (glFixOne Γ(T.unop, ⊤) d)ᵐᵒᵖ
        (FreeDimAlgebra Γ(T.unop, ⊤) d))) := sorry

/-- The fibrewise comparison isomorphism. -/
def fibreIso (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (AlgebraicGeometry.FA d).obj T ≅ (actionGroupoid d).obj T where
  hom := toAction Γ(T.unop, ⊤) d
  inv := fromAction Γ(T.unop, ⊤) d
  hom_inv_id := (fibreIso_laws d T).1
  inv_hom_id := (fibreIso_laws d T).2

/-- The forward fibre isomorphism sends an algebra arrow to its unit-fixing label. -/
theorem fibreIso_hom (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (fibreIso d T).hom = toAction Γ(T.unop, ⊤) d := rfl

private theorem isoActionGroupoid_naturality (d : ℕ) [NeZero d] :
    ∀ {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T'),
      (AlgebraicGeometry.FA d).map f ≫ (fibreIso d T').hom =
        (fibreIso d T).hom ≫ (actionGroupoid d).map f := sorry

/-- The natural isomorphism between free-algebra and action-groupoid presheaves. -/
def isoActionGroupoid (d : ℕ) [NeZero d] : AlgebraicGeometry.FA d ≅ actionGroupoid d :=
  NatIso.ofComponents (fun T ↦ fibreIso d T) (isoActionGroupoid_naturality d)

/-- The forward component of the natural isomorphism. -/
theorem isoActionGroupoid_hom_app (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (isoActionGroupoid d).hom.app T = (fibreIso d T).hom := rfl

/-- The inverse component of the natural isomorphism. -/
theorem isoActionGroupoid_inv_app (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (isoActionGroupoid d).inv.app T = (fibreIso d T).inv := rfl

/-- The scheme-point total arrow equivalence. -/
def pointArrowEquiv (d : ℕ) [NeZero d] (T : Scheme) :
    glFixOne Γ(T, ⊤) d ×
        (T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) ≃
      (Σ m : FreeDimAlgebra Γ(T, ⊤) d, Σ m' : FreeDimAlgebra Γ(T, ⊤) d, m ⟶ m') :=
  (Equiv.prodCongr (Equiv.refl _)
      (UniversalFiniteFreeAlgebra.schemeHomEquiv T ⟨d, Nat.pos_of_neZero d⟩)).trans
    (arrowEquiv Γ(T, ⊤) d)

/-- The first coordinate of a scheme-point arrow is its group label. -/
theorem pointArrowEquiv_fst (d : ℕ) [NeZero d] (T : Scheme)
    (g : glFixOne Γ(T, ⊤) d)
    (f : T ⟶ UniversalFiniteFreeAlgebra.baseScheme ⟨d, Nat.pos_of_neZero d⟩) :
    ((pointArrowEquiv d T).symm
        (arrowEquiv Γ(T, ⊤) d (g, UniversalFiniteFreeAlgebra.schemeHomEquiv T
          ⟨d, Nat.pos_of_neZero d⟩ f))).1 = g := by
  change ((arrowEquiv Γ(T, ⊤) d).symm
    (arrowEquiv Γ(T, ⊤) d (g, UniversalFiniteFreeAlgebra.schemeHomEquiv T
      ⟨d, Nat.pos_of_neZero d⟩ f))).1 = g
  rw [Equiv.symm_apply_apply]

end FA
end AlgebraicGeometry
