/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap59.Lemma_59_71_7
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Constructible abelian étale sheaves whose support is contained in a closed subset missing a
fixed point `η`. -/
def IsConstructibleEtaleAddCommGrp.SupportAway
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (η : X) :
    ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  fun G ↦ IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant G ∧
    ∃ Z : Closeds X, η ∉ Z ∧ abelianSheafSupport G ⊆ (Z : Set X)

/-- Unfolding of `IsConstructibleEtaleAddCommGrp.SupportAway`. -/
theorem IsConstructibleEtaleAddCommGrp.SupportAway_iff
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (η : X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleEtaleAddCommGrp.SupportAway restrict finiteLocallyConstant η G ↔
      IsConstructibleEtaleAddCommGrp restrict finiteLocallyConstant G ∧
        ∃ Z : Closeds X, η ∉ Z ∧ abelianSheafSupport G ⊆ (Z : Set X) :=
  sorry

/-- Lemma 59.73.14 (1): on a quasi-compact quasi-separated scheme `X`, a torsion abelian étale
sheaf with vanishing geometric stalk at a geometric generic point of an irreducible component
is a filtered colimit of constructible abelian sheaves whose supports lie in closed subschemes
not containing that generic point. -/
@[stacks 0F0M]
theorem isConstructibleEtaleAddCommGrp_ind_supportAway
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} →
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (ηbar : Scheme.GeometricPoint X)
    (hη : IsGenericPoint ηbar.image (irreducibleComponent ηbar.image))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F)
    (h0 : IsZero (geometricStalkAddCommGrp F ηbar)) :
    ObjectProperty.ind.{u}
      (IsConstructibleEtaleAddCommGrp.SupportAway restrict finiteLocallyConstant ηbar.image) F :=
  sorry

/-- Constructible étale sheaves of modules whose support is contained in a closed subset missing a
fixed point `η`. -/
def IsConstructibleEtaleModule.SupportAway
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) → Prop)
    (η : X) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun G ↦ IsConstructibleEtaleModule restrict finiteTypeLocallyConstant G ∧
    ∃ Z : Closeds X, η ∉ Z ∧ moduleSheafSupport G ⊆ (Z : Set X)

/-- Unfolding of `IsConstructibleEtaleModule.SupportAway`. -/
theorem IsConstructibleEtaleModule.SupportAway_iff
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) → Prop)
    (η : X) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModule.SupportAway restrict finiteTypeLocallyConstant η G ↔
      IsConstructibleEtaleModule restrict finiteTypeLocallyConstant G ∧
        ∃ Z : Closeds X, η ∉ Z ∧ moduleSheafSupport G ⊆ (Z : Set X) :=
  sorry

/-- Lemma 59.73.14 (2): on a quasi-compact quasi-separated scheme `X` and a Noetherian ring `Λ`,
a sheaf of `Λ`-modules on `Xₑₜ` with vanishing geometric stalk at a geometric generic point of
an irreducible component is a filtered colimit of constructible sheaves of `Λ`-modules whose
supports lie in closed subschemes not containing that generic point. -/
@[stacks 0F0M]
theorem isConstructibleEtaleModule_ind_supportAway
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) →
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) → Prop)
    (ηbar : Scheme.GeometricPoint X)
    (hη : IsGenericPoint ηbar.image (irreducibleComponent ηbar.image))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h0 : IsZero (geometricStalkModule F ηbar)) :
    ObjectProperty.ind.{u}
      (IsConstructibleEtaleModule.SupportAway restrict finiteTypeLocallyConstant ηbar.image) F :=
  sorry

end CategoryTheory.Sheaf
