/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Local criteria for geometric irreducibility

This leaf packages the section-ring and open-cover criteria for a scheme over a
field. The section algebra is inherited from the canonical global-sections
owner, while the geometric predicates and their transport theorems live here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The section ring of an open subscheme is geometrically irreducible over the base field. -/
@[stacks 038G]
def sections (U : X.Opens) : Prop :=
  GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (f.sectionsMap U)))

/-- An open cover is geometrically irreducible when its members are geometrically irreducible and
every pair of member ranges intersects nontrivially. -/
@[stacks 038G]
def IsOpenCover
    (𝒰 : Scheme.OpenCover.{u} X) : Prop :=
  (∀ i : 𝒰.I₀, GeometricallyIrreducible ((𝒰.f i) ≫ f)) ∧
    ∀ i j : 𝒰.I₀,
      (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.Opens) : Set X).Nonempty

/-- Geometric irreducibility is equivalent to geometric irreducibility of every nonempty affine
open's section ring. -/
@[stacks 038G]
theorem iff_forall_nonempty_affineOpen_sections
    :
    GeometricallyIrreducible f ↔
      ∀ U : X.affineOpens,
        (U : Set X).Nonempty →
          sections f (U : X.Opens) := sorry

/-- Geometric irreducibility is equivalent to irreducibility together with an affine open cover
whose section rings are geometrically irreducible. -/
@[stacks 038G]
theorem iff_irreducibleSpace_and_exists_affineOpenCover
    :
    GeometricallyIrreducible f ↔
      IrreducibleSpace X ∧
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            sections f (𝒰.f i).opensRange := sorry

/-- Geometric irreducibility is equivalent to a nonempty open cover by geometrically irreducible
open subschemes with nonempty pairwise intersections. -/
@[stacks 038G]
theorem iff_exists_openCover
    :
    GeometricallyIrreducible f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} X,
        Nonempty 𝒰.I₀ ∧ IsOpenCover f 𝒰 := sorry

/-- A nonempty open subscheme of a geometrically irreducible scheme over a field is geometrically
irreducible over the same field. -/
@[stacks 038G]
theorem of_nonempty_open
    (hf : GeometricallyIrreducible f) (U : X.Opens) (hU : (U : Set X).Nonempty) :
    GeometricallyIrreducible (U.ι ≫ f) := sorry

end

end GeometricallyIrreducible

end AlgebraicGeometry
