module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_1_AlgClosedPoints

/-!
# Surjectivity of locally finite type morphisms of algebraic spaces

A locally-of-finite-type morphism of algebraic spaces is surjective if and only
if it is surjective on algebraically closed field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.24.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. The following
are equivalent: `f` is surjective, and for every algebraically closed field `k`
over `S` the induced map `X(k) → Y(k)` is surjective. -/
@[stacks 0487]
theorem surjective_iff_surjectiveOnAlgClosedPoints
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    Surjective f ↔ surjectiveOnAlgClosedPoints f :=
  sorry

namespace Surjective

/-- A locally-of-finite-type morphism of algebraic spaces that is surjective on
algebraically closed field-valued points is surjective. -/
theorem of_surjectiveOnAlgClosedPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] (h : surjectiveOnAlgClosedPoints f) :
    Surjective f :=
  sorry

end Surjective

namespace surjectiveOnAlgClosedPoints

/-- A locally-of-finite-type surjective morphism of algebraic spaces is
surjective on algebraically closed field-valued points. -/
theorem of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] :
    surjectiveOnAlgClosedPoints f :=
  sorry

end surjectiveOnAlgClosedPoints

end AlgebraicGeometry.AlgebraicSpace
