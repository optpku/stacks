module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian

/-!
# Étale field-valued covers of DM residual gerbes

A DM, locally Noetherian, reduced algebraic stack whose space of points is a
singleton admits a surjective étale morphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a field `k` and a surjective étale morphism
`GroupoidsOver.slice (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsSurjectiveEtaleSpecField {S : Scheme.{u}} (Z : GroupoidsOver S)
    [AlgebraicStack Z] : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
    Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Etale f

namespace existsSurjectiveEtaleSpecField

/-- `existsSurjectiveEtaleSpecField Z` unpacks to a field `k` and a surjective
étale morphism from `Spec (.of k)` to `Z` over `S`. -/
theorem iff {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    existsSurjectiveEtaleSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Etale f :=
  sorry

/-- A surjective étale morphism from `Spec (.of k)` witnesses
`existsSurjectiveEtaleSpecField`. -/
theorem of {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z) [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Etale f] : existsSurjectiveEtaleSpecField Z :=
  sorry

/-- `existsSurjectiveEtaleSpecField Z` supplies a field `k` and a surjective
étale morphism from `Spec (.of k)` to `Z`. -/
theorem spec {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    (h : existsSurjectiveEtaleSpecField Z) :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
      (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
      Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Etale f :=
  sorry

end existsSurjectiveEtaleSpecField

/-- A DM, locally Noetherian, reduced algebraic stack with a singleton space
of points admits a surjective étale morphism from the spectrum of a field. -/
@[stacks 06N0]
theorem existsSurjectiveEtaleSpecField_of_isDM {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [IsDM Z] [IsLocallyNoetherian Z]
    [IsReduced Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    existsSurjectiveEtaleSpecField Z :=
  sorry

/-- `existsSurjectiveEtaleSpecField Z` is equivalent to the existence of a
field-valued point whose morphism is surjective and étale. -/
theorem existsSurjectiveEtaleSpecField_iff_fieldValuedPoint {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    existsSurjectiveEtaleSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.Surjective p.hom ∧ Groupoids.Hom.Etale p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
