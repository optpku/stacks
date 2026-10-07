module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.Triangulated
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated closure of perfect derived modules

Perfect objects in the derived category of modules over a ring form a triangulated object
property.  The objectwise two-out-of-three consequences are exposed alongside the canonical
instance.

@stack 066R
-/

@[expose] public section

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u

namespace DerivedCategory.IsPerfect

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-- Shifts preserve perfect derived module objects. -/
@[stacks 066R "shift stability of perfect derived modules"]
theorem shift {K : DMod} (hK : K.IsPerfect) (n : ℤ) :
    (K⟦n⟧).IsPerfect := sorry
-- Proof strategy: choose a bounded finite-projective complex representing `K`, shift that complex,
-- use the imported shift stability of `CochainComplex.IsBoundedFiniteProjective`, and transport the
-- resulting derived isomorphism to `K⟦n⟧`.

/-- Lemma 15.75.4 (066R): perfect derived module objects form a triangulated object property. -/
@[stacks 066R "triangulated closure"]
instance isTriangulated :
    ObjectProperty.IsTriangulated
      (_root_.DerivedCategory.IsPerfect : ObjectProperty DMod) := sorry
-- Proof strategy: construct the triangulated-property fields using the zero perfect complex,
-- `shift`, and mapping-cone closure for bounded finite-projective representatives; transport each
-- statement along the derived localization isomorphisms.

/-- The third vertex of a distinguished triangle is perfect when the first two vertices are. -/
@[stacks 066R "third vertex"]
theorem obj₃ (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPerfect) (h₂ : T.obj₂.IsPerfect) :
    T.obj₃.IsPerfect := sorry
-- Proof strategy: apply the third-vertex closure operation supplied by the canonical
-- `ObjectProperty.IsTriangulated` instance to `hT`, `h₁`, and `h₂`.

/-- The second vertex of a distinguished triangle is perfect when the first and third are. -/
@[stacks 066R "second vertex"]
theorem obj₂ (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPerfect) (h₃ : T.obj₃.IsPerfect) :
    T.obj₂.IsPerfect := sorry
-- Proof strategy: rotate `T`, apply `obj₃` to the rotated distinguished triangle, and transport
-- perfectness across the canonical shift isomorphism.

/-- The first vertex of a distinguished triangle is perfect when the second and third are. -/
@[stacks 066R "first vertex"]
theorem obj₁ (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsPerfect) (h₃ : T.obj₃.IsPerfect) :
    T.obj₁.IsPerfect := sorry
-- Proof strategy: rotate `T` twice, apply `obj₃`, and use shift stability to identify the resulting
-- shifted first vertex with `T.obj₁`.

end DerivedCategory.IsPerfect
