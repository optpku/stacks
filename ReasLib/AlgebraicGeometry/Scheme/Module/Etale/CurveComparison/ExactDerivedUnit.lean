/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DerivedResolutionComparison
public import Mathlib.Algebra.Homology.Single

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w

namespace ActualResolutionComparison
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

/-- The single-object coefficient map has identity component in degree zero. -/
def singleCoefficientMap (M : C) :
    (CochainComplex.single₀ D).obj (F.obj M) ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ C).obj M) :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨𝟙 _, sorry⟩

/-- The actual derived unit on a coefficient in degree zero, constructed from
the single-object map, extension comparison, and bounded-derived unit. -/
def underivedToDerived (M : C) : singleModel (F.obj M) ⟶
    (Functor.RightDerived.Bounded.functor F).obj (singleModel M) :=
  DerivedCategory.Plus.Q.map ((CochainComplex.Plus.extendNat D).map (singleCoefficientMap F M)) ≫
    Functor.RightDerived.Bounded.fromCochainMap F
      (ObjectProperty.homMk (ComplexShape.embeddingUpNat.mapAppIso F
        ((CochainComplex.single₀ C).obj M)).inv)

/-- Exact functors have invertible derived units on degree-zero objects. -/
instance underivedToDerived_isIso [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : C) :
    IsIso (underivedToDerived F M) := sorry

/-- The exact-functor comparison inverts only the specified single-object derived unit. -/
def exactUnitIso [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : C) :=
  @asIso _ _ _ _ (underivedToDerived F M) (underivedToDerived_isIso F M)

end ActualResolutionComparison
