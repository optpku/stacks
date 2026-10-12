/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Commutation
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

/- Lemma 42.46.6 (1): every defined Chern component of a perfect derived module is
central in the full operational Chow cohomology ring. -/
@[stacks 0FAC]
#check
  (AlgebraicGeometry.ChernClass.Derived.component_mem_center :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
      (cE : ∀ i : ℕ, ChowCohomology.degree δ π (i : ℤ))
      (complexChernClass :
        ∀ (Y : Over S) [LocallyOfFiniteType Y.hom],
          CochainComplex Y.left.Modules ℤ → ∀ i : ℕ,
            ChowCohomology.degree δ Y.hom (i : ℤ))
      (hDefined :
        ∃ (Y : Over S) (f : Y ⟶ Over.mk π),
          IsEnvelope f.left ∧
            RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
              ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E))
      (hChernClass :
        ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
          (f : Y ⟶ Over.mk π) (Q : CochainComplex Y.left.Modules ℤ),
          IsEnvelope f.left →
            IsIsomorphic (DerivedCategory.Q.obj Q)
              ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E) →
            RingedSpace.CochainComplex.IsLocallyBoundedAbove Q →
            RingedSpace.CochainComplex.IsLocallyBoundedBelow Q →
            (∀ n, Scheme.Modules.IsFiniteLocallyFree (Q.X n)) →
            ∀ i : ℕ, ChowCohomology.restrictDegree δ f (i : ℤ) (cE i) =
              complexChernClass Y Q i)
      (complexChernClass_pullback :
        ∀ {Y Z : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
          (f : Y ⟶ Z) (Q : CochainComplex Z.left.Modules ℤ) (i : ℕ),
          ChowCohomology.restrictDegree δ f (i : ℤ) (complexChernClass Z Q i) =
            complexChernClass Y
              (((Scheme.Modules.pullback f.left).mapHomologicalComplex (up ℤ)).obj Q) i)
      (complexChernClass_commute :
        ∀ {Y Z : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
          (f : Y ⟶ Z) (Q : CochainComplex Z.left.Modules ℤ) (r : ℤ → ℕ),
          CochainComplex.bounded Z.left.Modules Q →
            (∀ n, Scheme.Modules.IsFiniteLocallyFreeOfRank (r n) (Q.X n)) →
            ∀ (i : ℕ) (q : ℤ) (c : BivariantClass δ f q),
              BivariantClass.Commute δ f (𝟙 Z) c (complexChernClass Z Q i)),
      DirectSum.of (ChowCohomology.degree δ π) (p : ℤ) (cE p) ∈
        Set.center (ChowCohomology.ring δ π))

/- Lemma 42.46.6 (2): every bivariant class commutes with a defined Chern component
of a perfect derived module after locally finite-type pullback. -/
@[stacks 0FAC]
#check
  (AlgebraicGeometry.ChernClass.Derived.component_commute :
    ∀ {S X X' : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (p : ℕ)
      (cE : ∀ i : ℕ, ChowCohomology.degree δ π (i : ℤ))
      (complexChernClass :
        ∀ (Y : Over S) [LocallyOfFiniteType Y.hom],
          CochainComplex Y.left.Modules ℤ → ∀ i : ℕ,
            ChowCohomology.degree δ Y.hom (i : ℤ))
      (hDefined :
        ∃ (Y : Over S) (f : Y ⟶ Over.mk π),
          IsEnvelope f.left ∧
            RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
              ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E))
      (hChernClass :
        ∀ {Y : Over S} [LocallyOfFiniteType Y.hom]
          (f : Y ⟶ Over.mk π) (Q : CochainComplex Y.left.Modules ℤ),
          IsEnvelope f.left →
            IsIsomorphic (DerivedCategory.Q.obj Q)
              ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E) →
            RingedSpace.CochainComplex.IsLocallyBoundedAbove Q →
            RingedSpace.CochainComplex.IsLocallyBoundedBelow Q →
            (∀ n, Scheme.Modules.IsFiniteLocallyFree (Q.X n)) →
            ∀ i : ℕ, ChowCohomology.restrictDegree δ f (i : ℤ) (cE i) =
              complexChernClass Y Q i)
      (complexChernClass_pullback :
        ∀ {Y Z : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
          (f : Y ⟶ Z) (Q : CochainComplex Z.left.Modules ℤ) (i : ℕ),
          ChowCohomology.restrictDegree δ f (i : ℤ) (complexChernClass Z Q i) =
            complexChernClass Y
              (((Scheme.Modules.pullback f.left).mapHomologicalComplex (up ℤ)).obj Q) i)
      (complexChernClass_commute :
        ∀ {Y Z : Over S} [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
          (f : Y ⟶ Z) (Q : CochainComplex Z.left.Modules ℤ) (r : ℤ → ℕ),
          CochainComplex.bounded Z.left.Modules Q →
            (∀ n, Scheme.Modules.IsFiniteLocallyFreeOfRank (r n) (Q.X n)) →
            ∀ (i : ℕ) (q : ℤ) (c : BivariantClass δ f q),
              BivariantClass.Commute δ f (𝟙 Z) c (complexChernClass Z Q i))
      (g : X' ⟶ X) [LocallyOfFiniteType g] (q : ℤ)
      (c : BivariantClass δ
        (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) q),
      BivariantClass.Commute δ
        (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) (𝟙 (Over.mk π)) c (cE p))

end AlgebraicGeometry.ChernClass
