/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import stacks_project.Chap59.Definition_59_57_2
public import stacks_project.Chap59.Lemma_59_56_5
public import stacks_project.Chap59.Lemma_59_59_1
public import stacks_project.Chap59.Lemma_59_59_2_DerivedInvariants
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology

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

/-- Stalk extraction of abelian étale sheaves is additive. -/
instance stalkGaloisModule_additive :
    (stalkGaloisModule K s).Additive := sorry

/-- Stalk extraction of abelian étale sheaves preserves finite limits. -/
instance stalkGaloisModule_preservesFiniteLimits :
    PreservesFiniteLimits (stalkGaloisModule K s) := sorry

/-- Stalk extraction of abelian étale sheaves preserves finite colimits. -/
instance stalkGaloisModule_preservesFiniteColimits :
    PreservesFiniteColimits (stalkGaloisModule K s) := sorry

/-- The composite `Γ_G ∘ stalk` is additive. -/
instance stalkGaloisModule_comp_invariantsFunctor_additive :
    (stalkGaloisModule K s ⋙
      DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).Additive :=
  inferInstance

/-- Stalk extraction of abelian étale sheaves preserves injective objects. -/
instance stalkGaloisModule_preservesInjectiveObjects :
    (stalkGaloisModule K s).PreservesInjectiveObjects :=
  inferInstance

/-- Bundled exact-functor view of stalk extraction preserves injective objects. -/
instance stalkGaloisModuleExact_preservesInjectiveObjects :
    (ExactFunctor.of (stalkGaloisModule K s)).obj.PreservesInjectiveObjects :=
  stalkGaloisModule_preservesInjectiveObjects K s

/-- The identity object of the small étale site is the terminal étale object. -/
def globalEtale_isTerminal (X : Scheme.{u}) :
    IsTerminal (globalEtale X) :=
  MorphismProperty.Over.mkIdTerminal @Etale X

/-- Restriction of global abelian étale sections to the stalk at the geometric
point determined by `κ(s)^sep`. -/
def etaleAbelianSectionsToStalk
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F ⟶
      stalkAddCommGrp K s F :=
  (etalePoint K s).toPresheafFiber (globalEtale (Spec (.of K)))
    (Over.homMk (geometricPointHom K s)) F.obj

/-- Degree-zero étale cohomology as global abelian sections at the terminal
object of the small étale site. -/
def etaleH0IsoGlobalSections
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    (Sheaf.functorH (Spec (.of K)).smallEtaleTopology 0).obj F ≅
      (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F :=
  (Sheaf.H.equiv₀ F (globalEtale_isTerminal (Spec (.of K)))).toAddCommGrpIso

/-- Forward comparison from global abelian sections to Galois invariants of the
corresponding discrete continuous stalk module. -/
def etaleAbelianSectionsToGaloisInvariants
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F ⟶
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj
        ((stalkGaloisModule K s).obj F) :=
  let φ :=
    ((etaleAbelianSectionsToStalk K s F).hom.toIntLinearMap).codRestrict
      (((Rep.ActionToRep ℤ s.absoluteGaloisGroup).obj
          ((stalkGaloisModule K s).obj F).obj).ρ.invariants)
      (fun _ _ ↦ sorry)
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (ModuleCat.ofHom φ)

/-- Reverse comparison from Galois invariants of the stalk module to global
abelian sections, as the inverse of the abelian upgrade of
`globalSectionsEquivGaloisInvariants`. -/
def etaleGaloisInvariantsToAbelianSections
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj
        ((stalkGaloisModule K s).obj F) ⟶
      (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F :=
  AddCommGrpCat.ofHom
    { toFun :=
        (Equiv.ofBijective
          (fun x ↦ (etaleAbelianSectionsToGaloisInvariants K s F).hom x) sorry).symm
      map_zero' := sorry
      map_add' := sorry }

/-- Abelian upgrade of Lemma 59.56.5: global sections of an abelian étale sheaf
identified with Galois invariants of the stalk module. -/
def etaleAbelianSectionsIsoGaloisInvariants
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    (siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K)))).obj F ≅
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj
        ((stalkGaloisModule K s).obj F) where
  hom := etaleAbelianSectionsToGaloisInvariants K s F
  inv := etaleGaloisInvariantsToAbelianSections K s F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Underived functorial comparison `Γ(S, -) ≅ Γ_G(-_s̄)` on abelian étale
sheaves of `Spec K`. -/
def etaleSectionsIsoGaloisInvariantsNatIso
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}] :
    siteAbelianSectionsFunctor (Spec (.of K)).smallEtaleTopology
        (globalEtale (Spec (.of K))) ≅
      stalkGaloisModule K s ⋙
        DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup :=
  NatIso.ofComponents (fun G ↦ etaleAbelianSectionsIsoGaloisInvariants K s G)
    (fun {G₁ G₂} f ↦ sorry)

/-- Helper: `RΓ(S, F) ≅ R(Γ_G ∘ stalk)(F[0])` from the underived identification
`Γ(S, -) ≅ Γ_G(-_s̄)` of Lemma 59.56.5. -/
def etaleDerivedSectionsIsoComposite
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

/-- Helper: `R(Γ_G ∘ stalk)(F[0]) ≅ RΓ_G((F_s̄)[0])` by commuting exact stalk
extraction past derived invariants. -/
def etaleDerivedCompositeIsoDerivedInvariants
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
      (ExactFunctor.of (stalkGaloisModule K s))
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup)).symm.app
    ((DerivedCategory.singleFunctor
        (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) 0).obj F) ≪≫
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).mapIso
      (((stalkGaloisModule K s).mapDerivedCategorySingleFunctor 0).app F)

/-- Lemma 59.59.2 (1): with the setup of Lemma 59.59.1, if an abelian sheaf `F` on
`Spec K` étale corresponds to the discrete continuous Galois module `M`, then
there is a canonical isomorphism `RΓ(S, F) ≅ RΓ_G(M)` in the derived category of
abelian groups. -/
@[stacks 03QU]
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
          (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).obj M) :=
  etaleDerivedSectionsIsoComposite K s F ≪≫
    etaleDerivedCompositeIsoDerivedInvariants K s F ≪≫
    (DiscreteModuleCat.derivedInvariants s.absoluteGaloisGroup).mapIso
      ((DerivedCategory.singleFunctor (DiscreteModuleCat ℤ s.absoluteGaloisGroup) 0).mapIso e)

/-- Lemma 59.59.2 (2): étale cohomology in degree `0` is canonically isomorphic
to the Galois invariants of the corresponding discrete continuous module (the
abelian upgrade of Lemma 59.56.5). -/
@[stacks 03QU]
def etaleH0IsoGaloisInvariants
    (M : DiscreteModuleCat ℤ s.absoluteGaloisGroup)
    (e : (stalkGaloisModule K s).obj F ≅ M)
    [HasSheafify (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})] :
    (Sheaf.functorH (Spec (.of K)).smallEtaleTopology 0).obj F ≅
      (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).obj M :=
  etaleH0IsoGlobalSections K F ≪≫
    etaleAbelianSectionsIsoGaloisInvariants K s F ≪≫
    (DiscreteModuleCat.invariantsFunctor s.absoluteGaloisGroup).mapIso e

/-- Forgotten continuous Galois cohomology, as an abelian group. -/
abbrev continuousCohomologyAddCommGrp
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat ℤ G) (q : ℕ) : AddCommGrpCat.{u} :=
  (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙
    forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
    (DiscreteModuleCat.continuousCohomology G M q)

/-- Homology of the canonical derived comparison of Lemma 59.59.2 (1). -/
def etaleDerivedHomologyIsoGalois (q : ℕ)
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

/-- Lemma 59.59.2 (3): étale cohomology in degree `q` is canonically isomorphic
to continuous Galois cohomology of the corresponding discrete continuous module. -/
@[stacks 03QU]
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
      (continuousCohomologyAddCommGrp s.absoluteGaloisGroup M q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
