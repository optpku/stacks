module

public import ReasLib.Algebra.Homology.DerivedCategory.Resolution.Hom
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact functors and derived Hom computed by K-injective targets

This leaf isolates the functorial part of the K-injective Hom-complex comparison.  A source
complex is sent through an additive functor preserving finite limits and finite colimits; when the
image of the target is K-injective, degree-zero Hom-complex cohomology computes morphisms between
the images in the derived categories.  Geometric specializations, such as restriction to an
open object of a ringed site, belong in their own leaves.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory

noncomputable section

universe wA wB vA vB uA uB

namespace CochainComplex.Resolution

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- An additive exact functor transports the degree-`n` K-injective Hom-complex equivalence to the
corresponding shifted derived morphism group. -/
@[stacks 0CS5 "exact-functor degree-n K-injective Hom equivalence"]
noncomputable def mapHomologyAddEquiv
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L I : CochainComplex A ℤ)
    [IsKInjective ((F.mapHomologicalComplex (up ℤ)).obj I)] (n : ℤ) :
    (CochainComplex.HomComplex
      ((F.mapHomologicalComplex (up ℤ)).obj L)
      ((F.mapHomologicalComplex (up ℤ)).obj I)).homology n ≃+
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L) ⟶
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj I))⟦n⟧) :=
  (injectiveHomologyAddEquiv
      ((F.mapHomologicalComplex (up ℤ)).obj L)
      ((F.mapHomologicalComplex (up ℤ)).obj I) n).trans
    (Iso.homCongrAddEquiv
      ((F.mapDerivedCategoryFactors.app L).symm)
      (asIso (((F.mapDerivedCategoryFactors.app I).symm.hom)⟦n⟧')))

/-- Lemma 21.34.6 (2): an additive exact functor transports the degree-zero K-injective
Hom-complex equivalence to the corresponding derived morphism group. -/
@[stacks 0A94 "exact-functor degree-zero K-injective Hom equivalence"]
noncomputable def mapHomologyZeroAddEquiv
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L I : CochainComplex A ℤ)
    [IsKInjective ((F.mapHomologicalComplex (up ℤ)).obj I)] :
    (CochainComplex.HomComplex
      ((F.mapHomologicalComplex (up ℤ)).obj L)
      ((F.mapHomologicalComplex (up ℤ)).obj I)).homology (0 : ℤ) ≃+
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L) ⟶
          F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) :=
  (mapHomologyAddEquiv F L I 0).trans
    (Iso.homCongrAddEquiv (Iso.refl _)
      ((shiftFunctorZero (DerivedCategory B) ℤ).app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj I))))

end CochainComplex.Resolution
