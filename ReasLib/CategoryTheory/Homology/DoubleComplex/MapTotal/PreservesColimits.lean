module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal

/-!
# Functors preserving unbounded total complexes

The total complex of a double complex is formed degreewise from coproducts over the fibres of
the total-degree map.  This file isolates the exact preservation hypothesis under which the
canonical comparison between mapping and totalizing is invertible.  In particular, it applies
to left adjoints without imposing a finite-support condition on the double complex.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂ w₁ w₂ w₁₂

namespace HomologicalComplex₂.Total.Map.Comparison

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (K : HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂] [K.HasTotal c₁₂]
variable [((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c₁₂]

/-- The precise condition that `F` preserves every coproduct used in the total degrees of `K`.
This is deliberately finer than preservation of all coproducts and does not require boundedness
or finite support. -/
@[stacks 0132 "total-degree coproduct preservation"]
abbrev PreservesTotalDegreeCoproducts : Prop :=
  ∀ n : I₁₂, PreservesColimit
    (Discrete.functor
      (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c₁₂) n)) F

/-- If `F` preserves the coproduct defining a total degree, then the canonical comparison in
that degree is invertible. -/
@[stacks 0132 "preserved total-degree comparison"]
theorem component_isIso_of_preservesTotalDegreeCoproducts
    [PreservesTotalDegreeCoproducts F K c₁₂] (n : I₁₂) :
    IsIso (component F K c₁₂ n) := sorry

/-- An additive functor preserving all coproducts used by a double complex commutes with its
possibly unbounded total complex. -/
@[stacks 07A4 "pullback commutes with unbounded totalization"]
theorem isIso_of_preservesTotalDegreeCoproducts
    [PreservesTotalDegreeCoproducts F K c₁₂] :
    IsIso (hom F K c₁₂) := sorry

/-- Preservation of all colimits of the relevant universe implies preservation of the
coproducts in every total degree. -/
@[stacks 0132 "cocontinuous functors commute with totalization"]
theorem isIso_of_preservesColimits
    [PreservesColimitsOfSize.{max w₁ w₂, max w₁ w₂} F] :
    IsIso (hom F K c₁₂) := sorry

end HomologicalComplex₂.Total.Map.Comparison
