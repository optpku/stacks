module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open scoped GrothendieckTopologyDerivedSections

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.59.2 (1): Derived global sections of an abelian étale sheaf over a field spectrum are
canonically isomorphic to total derived invariants of its identified Galois stalk module. -/
@[stacks 03QU] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedSectionsIsoGalois :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (M : DiscreteModuleCat ℤ s.absoluteGaloisGroup)
    (e : (stalkGaloisModule K s).obj F ≅ M)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
          (globalEtale (Spec (.of K)))))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [CategoryWithHomology (DiscreteModuleCat ℤ s.absoluteGaloisGroup)]
    [HasDerivedCategory (DiscreteModuleCat ℤ s.absoluteGaloisGroup)]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
      (HomologicalComplex.quasiIso
        (DiscreteModuleCat ℤ s.absoluteGaloisGroup) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (stalkGaloisModule K s ⋙
          DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))],
    (siteAbelianSectionsDerived (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj
      ((DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) ≅
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).obj
      ((DerivedCategory.singleFunctor
          (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).obj M))

/- Lemma 59.59.2 (2): Degree-zero étale cohomology is canonically isomorphic to the abelian group of
invariants of the identified Galois stalk module. -/
@[stacks 03QU] #check (AlgebraicGeometry.Scheme.Etale.etaleH0IsoGaloisInvariants :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (M : DiscreteModuleCat ℤ s.absoluteGaloisGroup)
    (e : (stalkGaloisModule K s).obj F ≅ M)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})],
    (Sheaf.functorH (Spec (.of K)).smallEtaleTopology 0).obj F ≅
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj M)

/- Lemma 59.59.2 (3): Étale cohomology over a field spectrum is isomorphic in every nonnegative degree
to continuous cohomology of the identified discrete Galois stalk module. -/
@[stacks 03QU] #check (AlgebraicGeometry.Scheme.Etale.etaleCohomologyIsoGalois :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (q : ℕ)
    (M : DiscreteModuleCat ℤ s.absoluteGaloisGroup)
    (e : (stalkGaloisModule K s).obj F ≅ M)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
          (globalEtale (Spec (.of K)))))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [CategoryWithHomology (DiscreteModuleCat ℤ s.absoluteGaloisGroup)]
    [HasDerivedCategory (DiscreteModuleCat ℤ s.absoluteGaloisGroup)]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
      (HomologicalComplex.quasiIso
        (DiscreteModuleCat ℤ s.absoluteGaloisGroup) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (stalkGaloisModule K s ⋙
          DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))],
    IsIsomorphic
      ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology q).obj F)
      ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙
        forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        (DiscreteModuleCat.continuousCohomology s.absoluteGaloisGroup M q)))

end AlgebraicGeometry.Scheme.Etale
