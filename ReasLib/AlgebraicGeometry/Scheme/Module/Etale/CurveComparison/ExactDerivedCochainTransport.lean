/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ExactDerivedCochainTransport
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory C] [HasDerivedCategory D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (K L : CochainComplex C ℤ)

/-- Apply an exact functor to a specified derived arrow, using the canonical
localization compositor at both endpoints. -/
def map (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  (F.mapDerivedCategoryFactors.app K).inv ≫ F.mapDerivedCategory.map f ≫
    (F.mapDerivedCategoryFactors.app L).hom

end ExactDerivedCochainTransport
