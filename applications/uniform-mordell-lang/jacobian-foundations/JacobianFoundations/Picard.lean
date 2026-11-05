/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.AbelMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Pointed.Represented

/-!
# The Picard construction of the algebraic Jacobian

All data are built from the fppf-sheafified relative Picard functor.
The three explicit `sorry`s in this module are mathematical propositions:
the curve interface, representability of the degree-zero functor over an
arbitrary field, and the degree of the normalized graph class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.CurveJacobian.PicardConstruction

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- A curve in the challenge satisfies ReasLib's integral curve interface. -/
theorem targetCurve : Curve C := by
  sorry

attribute [local instance] targetCurve

/-- The degree-zero relative Picard functor of a smooth proper geometrically
irreducible curve is representable, over any ground field. -/
theorem degreeZeroRepresentable :
    (RelativePicard.degreeSubfunctor C 0).toFunctor.IsRepresentable := by
  sorry

attribute [local instance] degreeZeroRepresentable

/-- `Pic⁰(C/k)`, with its representing scheme chosen by representability. -/
noncomputable abbrev jacobian : Over (Spec (.of k)) :=
  RelativePicard.component C 0

/-- Tensor product, the trivial bundle, and duality induce the group scheme. -/
@[implicit_reducible]
noncomputable def groupStructure : GrpObj (jacobian C) :=
  RelativePicard.componentZeroGrpObj C

/-- The graph of a section gives a degree-one Hilbert point. -/
noncomputable def graphHilbertPoint {T : Over (Spec (.of k))} (x : T ⟶ C) :
    T ⟶ (Hilbert.functor C 1).reprX :=
  (Hilbert.functor C 1).representableBy.homEquiv.symm (Hilbert.Point.ofSection x)

/-- The relative Picard class of the effective graph divisor of `x`, obtained
directly from the arbitrary-base graph interface, without a Hilbert representative. -/
noncomputable def sectionGroupClass {T : Over (Spec (.of k))} (x : T ⟶ C) :
    (RelativePicard.groupFunctor C).obj (op T) :=
  (RelativePicard.groupFunctorForgetIso C).inv.app _
    ((GrothendieckTopology.toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
      (RelativePicard.presheaf C)).app _ (RelativePicard.sectionClass C x))

/-- The class of `O(Δ − C × P)` on `C ×ₖ C`, relative to the first factor.
Multiplication and inverse in this group encode tensor product and duality. -/
noncomputable def normalizedClass (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (RelativePicard.groupFunctor C).obj (op C) :=
  sectionGroupClass C (𝟙 C) *
    (sectionGroupClass C (CartesianMonoidalCategory.toUnit C ≫ P))⁻¹

/-- Both graph divisors have fiber degree one, so their difference has degree zero. -/
theorem normalizedClass_degreeZero (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    normalizedClass C P ∈ RelativePicard.degreeZeroSectionSubgroup C (op C) := by
  sorry

/-- The morphism represented by the normalized graph class. On points it is
`Q ↦ [O(Q − P)]`. -/
noncomputable def ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    C ⟶ jacobian C :=
  (RelativePicard.degreeZeroGroupRepresentation C).homEquiv.symm
    ⟨normalizedClass C P, normalizedClass_degreeZero C P⟩

/-- The Abel–Jacobi morphism represents the normalized graph line bundle. -/
theorem ofCurve_represents (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (RelativePicard.degreeZeroGroupRepresentation C).homEquiv (ofCurve C P) =
      ⟨normalizedClass C P, normalizedClass_degreeZero C P⟩ :=
  (RelativePicard.degreeZeroGroupRepresentation C).homEquiv.apply_symm_apply _

end AlgebraicGeometry.CurveJacobian.PicardConstruction
