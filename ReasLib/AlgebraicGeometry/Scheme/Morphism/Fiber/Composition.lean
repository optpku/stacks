/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField

/-!
# Fibres of composite scheme morphisms

This leaf provides the canonical morphism from a fibre of a composite to the
corresponding fibre of its second factor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The square used to map the fibre of `f ≫ g` over `s` to the fibre of `g`
over `s`. -/
theorem compFiberToBaseFiber_condition {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiberι (f ≫ g) s ≫ f ≫ g =
      fiberToSpecResidueField (f ≫ g) s ≫ S.fromSpecResidueField s := sorry

/-- The canonical morphism from the fibre of `f ≫ g` over `s` to the fibre of
`g` over `s`. -/
noncomputable def compFiberToBaseFiber {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    fiber (f ≫ g) s ⟶ fiber g s :=
  pullback.lift
    (fiberι (f ≫ g) s ≫ f)
    (fiberToSpecResidueField (f ≫ g) s)
    (compFiberToBaseFiber_condition f g s)

/-- The composite-fibre map preserves the structure map to the residue-field
spectrum of `s`. -/
theorem compFiberToBaseFiber_fiberToSpecResidueField {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    compFiberToBaseFiber f g s ≫ fiberToSpecResidueField g s =
      fiberToSpecResidueField (f ≫ g) s := sorry

/-- The composite-fibre map sends the fibre inclusion to the original map
`f`. -/
theorem compFiberToBaseFiber_fiberι {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    compFiberToBaseFiber f g s ≫ fiberι g s =
      fiberι (f ≫ g) s ≫ f := sorry

end AlgebraicGeometry.Scheme.Hom
