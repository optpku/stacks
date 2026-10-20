/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisModule
public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisInvariants
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.RepresentationTheory.Homological.ContCohomology.DiscreteCochains
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
variable (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})

/-- The identity object of the small étale site is the terminal étale object. -/
private def globalEtale_isTerminal (X : Scheme.{u}) :
    IsTerminal (globalEtale X) :=
  MorphismProperty.Over.mkIdTerminal @Etale X

/-- Restriction of global abelian étale sections to the stalk at the geometric
point determined by `κ(s)^sep`. -/
private def etaleAbelianSectionsToStalk
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F ⟶
      stalkAddCommGrp K s F :=
  (etalePoint K s).toPresheafFiber (globalEtale (Spec (.of K)))
    (Over.homMk (geometricPointHom K s)) F.obj

/-- Degree-zero étale cohomology as global abelian sections at the terminal
object of the small étale site. -/
private def etaleH0IsoGlobalSections
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    (Sheaf.functorH (Spec (.of K)).smallEtaleTopology 0).obj F ≅
      (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F :=
  (Sheaf.H.equiv₀ F (globalEtale_isTerminal (Spec (.of K)))).toAddCommGrpIso

/-- The stalk germ of every global abelian section is fixed by the residue-field Galois action. -/
private theorem etaleAbelianSectionsToStalk_mem_invariants
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    (x : (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
      (globalEtale (Spec (.of K)))).obj F) :
    (etaleAbelianSectionsToStalk K s F).hom.toIntLinearMap x ∈
      (((Rep.ActionToRep ℤ s.absoluteGaloisGroup).obj
        ((stalkGaloisModule K s).obj F).obj).ρ.invariants) := sorry

/-- Forward comparison from global abelian sections to Galois invariants of the
corresponding discrete continuous stalk module. -/
private def etaleAbelianSectionsToGaloisInvariants
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F ⟶
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj
        ((stalkGaloisModule K s).obj F) :=
  let φ :=
    ((etaleAbelianSectionsToStalk K s F).hom.toIntLinearMap).codRestrict
      (((Rep.ActionToRep ℤ s.absoluteGaloisGroup).obj
          ((stalkGaloisModule K s).obj F).obj).ρ.invariants)
      (etaleAbelianSectionsToStalk_mem_invariants K s F)
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (ModuleCat.ofHom φ)

/-- Restriction to the stalk is a bijection from global abelian sections to invariant
stalk elements. -/
private theorem etaleAbelianSectionsToGaloisInvariants_bijective
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    Function.Bijective (etaleAbelianSectionsToGaloisInvariants K s F).hom := sorry

/-- Global abelian sections are additively isomorphic to the invariant stalk elements. -/
private def etaleAbelianSectionsIsoGaloisInvariants
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F ≅
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj
        ((stalkGaloisModule K s).obj F) :=
  (AddEquiv.ofBijective (etaleAbelianSectionsToGaloisInvariants K s F).hom
    (etaleAbelianSectionsToGaloisInvariants_bijective K s F)).toAddCommGrpIso

/-- Restriction of abelian sections to invariant stalk elements commutes with sheaf morphisms. -/
private theorem etaleAbelianSectionsToGaloisInvariants_natural
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    {F₁ F₂ : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (f : F₁ ⟶ F₂) :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).map f ≫
      etaleAbelianSectionsToGaloisInvariants K s F₂ =
    etaleAbelianSectionsToGaloisInvariants K s F₁ ≫
      (stalkGaloisModule K s ⋙
        DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).map f := sorry

/-- Underived functorial comparison `Γ(S, -) ≅ Γ_G(-_s̄)` on abelian étale
sheaves of `Spec K`. -/
private def etaleSectionsIsoGaloisInvariantsNatIso
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K))) ≅
      stalkGaloisModule K s ⋙
        DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup :=
  NatIso.ofComponents (fun G ↦ etaleAbelianSectionsIsoGaloisInvariants K s G)
    (fun {G₁ G₂} f ↦ etaleAbelianSectionsToGaloisInvariants_natural K s f)

/-- Derived global abelian sections identify with the total right derivation of
invariants composed with stalk extraction. -/
private def etaleDerivedSectionsIsoComposite
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
        (ComplexShape.up ℤ))] :
    (siteAbelianSectionsDerived (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj
      ((DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) ≅
    (RightDerived.Cochain.functor
        (stalkGaloisModule K s ⋙
          DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup)).obj
      ((DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) :=
  let τ :=
    isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleSectionsIsoGaloisInvariantsNatIso K s) (ComplexShape.up ℤ))
      DerivedCategory.Q
  (rightDerivedNatIso
        (RightDerived.Cochain.functor
          (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
            (globalEtale (Spec (.of K)))))
        (RightDerived.Cochain.functor
          (stalkGaloisModule K s ⋙
            DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
        (RightDerived.Cochain.unit
          (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
            (globalEtale (Spec (.of K)))))
        (RightDerived.Cochain.unit
          (stalkGaloisModule K s ⋙
            DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
        (HomologicalComplex.quasiIso
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
          (ComplexShape.up ℤ))
        τ).app
      ((DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)

/-- Total right derivation of invariants after stalk extraction agrees with derived
invariants of the stalk concentrated in degree zero. -/
private def etaleDerivedCompositeIsoDerivedInvariants
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (stalkGaloisModule K s ⋙
          DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
      (HomologicalComplex.quasiIso
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [CategoryWithHomology (DiscreteModuleCat ℤ s.absoluteGaloisGroup)]
    [HasDerivedCategory (DiscreteModuleCat ℤ s.absoluteGaloisGroup)]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup))
      (HomologicalComplex.quasiIso
        (DiscreteModuleCat ℤ s.absoluteGaloisGroup) (ComplexShape.up ℤ))] :
    (RightDerived.Cochain.functor
        (stalkGaloisModule K s ⋙
          DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup)).obj
      ((DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) ≅
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).obj
      ((DerivedCategory.singleFunctor
          (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).obj
        ((stalkGaloisModule K s).obj F)) :=
  (Cochain.ExactFirst.iso
      (dsimp% [ExactFunctor.of] (ExactFunctor.of (stalkGaloisModule K s)))
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup)).symm.app
    ((DerivedCategory.singleFunctor
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) ≪≫
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).mapIso
      (((stalkGaloisModule K s).mapDerivedCategorySingleFunctor 0).app F)

/-- Derived global sections of an abelian étale sheaf over a field spectrum are
canonically isomorphic to total derived invariants of its identified Galois stalk module. -/
@[no_expose]
def etaleDerivedSectionsIsoGalois
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
        (ComplexShape.up ℤ))] :
    (siteAbelianSectionsDerived (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj
      ((DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) ≅
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).obj
      ((DerivedCategory.singleFunctor
          (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).obj M) := by
  exact etaleDerivedSectionsIsoComposite K s F ≪≫
    etaleDerivedCompositeIsoDerivedInvariants K s F ≪≫
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).mapIso
      ((DerivedCategory.singleFunctor (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).mapIso e)

/-- Degree-zero étale cohomology is canonically isomorphic to the abelian group of
invariants of the identified Galois stalk module. -/
@[no_expose]
def etaleH0IsoGaloisInvariants
    (M : DiscreteModuleCat ℤ s.absoluteGaloisGroup)
    (e : (stalkGaloisModule K s).obj F ≅ M)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    (Sheaf.functorH (Spec (.of K)).smallEtaleTopology 0).obj F ≅
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj M := by
  exact etaleH0IsoGlobalSections K F ≪≫
    etaleAbelianSectionsIsoGaloisInvariants K s F ≪≫
    (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).mapIso e

/-- Forgotten continuous Galois cohomology, as an abelian group. -/
private abbrev continuousCohomologyAddCommGrp
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat ℤ G) (q : ℕ) : AddCommGrpCat.{u} :=
  (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙
    forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
    (DiscreteModuleCat.continuousCohomology G M q)

/-- Homology carries the derived sections comparison to an isomorphism in each degree. -/
private def etaleDerivedHomologyIsoGalois (q : ℕ)
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
        (ComplexShape.up ℤ))] :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
      ((siteAbelianSectionsDerived (Spec (.of K)).smallEtaleTopology
          (globalEtale (Spec (.of K)))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F)) ≅
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
      ((DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).obj
        ((DerivedCategory.singleFunctor
            (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).obj M)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).mapIso
    (etaleDerivedSectionsIsoGalois K s F M e)

/-- Étale cohomology over a field spectrum is isomorphic in every nonnegative degree
to continuous cohomology of the identified discrete Galois stalk module. -/
theorem etaleCohomologyIsoGalois (q : ℕ)
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
        (ComplexShape.up ℤ))] :
    IsIsomorphic
      ((Sheaf.functorH (Spec (.of K)).smallEtaleTopology q).obj F)
      ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙
        forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        (DiscreteModuleCat.continuousCohomology s.absoluteGaloisGroup M q)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
