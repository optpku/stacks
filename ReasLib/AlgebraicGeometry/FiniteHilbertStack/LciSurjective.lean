module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.LciCoproduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SurjectiveOnObjects

/-!
# Surjectivity of the positive-degree LCI Hilbert coproduct

Every field-valued target object has a positive-degree LCI Hilbert lift over the
same field, and the canonical coproduct forgetful morphism is surjective on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom renaming
  Flat → GroupoidFlat, LocallyOfFinitePresentation → GroupoidLocallyOfFinitePresentation,
  Surjective → GroupoidSurjective,
  SurjectiveOnObjects → GroupoidSurjectiveOnObjects
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- For a flat, surjective, locally finitely presented morphism of stacks representable
by algebraic spaces, the positive-degree LCI Hilbert coproduct is surjective on objects. -/
instance lciCoproduct.forgetToY.surjectiveOnObjects (F : 𝒳 ⟶ 𝒴)
    [GroupoidFlat (asGroupoidsOverMor F)]
    [GroupoidSurjective (asGroupoidsOverMor F)]
    [GroupoidLocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    GroupoidSurjectiveOnObjects
      (asGroupoidsOverMor (lciCoproduct.forgetToY F)) :=
  sorry

/-- Every field-valued object of `𝒴` over `Spec(k)` lifts to an LCI Hilbert
object of some degree `d ≥ 1` with the same test scheme `Spec(k)`, so no field
extension is required. -/
theorem exists_lciObj_over_field (F : 𝒳 ⟶ 𝒴)
    [GroupoidFlat (asGroupoidsOverMor F)]
    [GroupoidSurjective (asGroupoidsOverMor F)]
    [GroupoidLocallyOfFinitePresentation (asGroupoidsOverMor F)]
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ asGroupoidsOver 𝒴) :
    ∃ (d : ℕ) (_ : 0 < d) (ξ : Obj (asGroupoidsOverMor F) d)
      (hU : ξ.U = Over.mk σ),
      Obj.IsLci (asGroupoidsOverMor F) ξ ∧
        Nonempty
          (YonedaSlice.representative ξ.y ≅
            slice.pullback (eqToHom hU) y) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
