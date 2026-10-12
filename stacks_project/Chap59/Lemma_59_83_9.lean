/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_83_8
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

/-- The sheaf `j_! G` obtained by extending the underlying abelian étale sheaf of a
`ZMod ell`-module sheaf `G` by zero along an étale morphism. -/
public noncomputable abbrev extensionByZeroZModModule {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] {ell : ℕ}
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [U.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} (ZMod ell))) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (abelianExtensionByZero j).obj
    ((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})).obj G)

/-- Unfolding of `extensionByZeroZModModule`. -/
public theorem extensionByZeroZModModule_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] {ell : ℕ}
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [U.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} (ZMod ell))) :
    extensionByZeroZModModule j G =
      (abelianExtensionByZero j).obj
        ((sheafCompose U.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})).obj G) := sorry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)] [IsReduced X.left]
variable (ell : ℕ) [Fact (Nat.Prime ell)]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]

/-- Lemma 59.83.9: in Situation 59.83.1, if `X` is reduced, `j : U ⟶ X` is an open
immersion with `U` connected, `ell` is prime, and `G` is a finite locally constant
sheaf of `ZMod ell`-vector spaces on `U`, then statements (1)–(8) hold for
`F = j_! G`, encoded as `StatementsHold` for `extensionByZeroZModModule j G`. -/
@[stacks 03SD]
public theorem statementsHold_of_isReduced_extensionByZeroZModModule
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] [ConnectedSpace U]
    [∀ H : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension H]
    [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    [U.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})]
    [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} (ZMod ell))]
    [∀ V : U.Etale,
      HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} (ZMod ell))]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} (ZMod ell)))
    [IsLocallyConstantWith
      (fun M : ModuleCat.{u} (ZMod ell) ↦ Module.Finite (ZMod ell) M) G]
    (finiteLocallyConstant :
      (Y : Scheme.{u}) → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} → Prop)
    (pullbackH :
      (Y : Scheme.{u}) → (f : Y ⟶ X.left) →
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] →
        [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})] →
        [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})] →
        [HasTerminal Y.Etale] →
        [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive] →
        (q : ℕ) →
        etaleCohomology X.left (extensionByZeroZModModule j G) q ⟶
          etaleCohomology Y
            ((etaleAbelianRestriction f).obj (extensionByZeroZModModule j G)) q)
    (h_finite : ∀ (Y : Scheme.{u}) (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
      finiteLocallyConstant Y H ↔ IsFiniteLocallyConstantAddCommGrp H)
    (h_pullback :
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X.left)
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
        [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
        [HasTerminal Y.Etale]
        [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
        [(etaleAbelianRestriction f).Additive]
        [(etaleAbelianRestriction f).PreservesHomology]
        [(etaleAbelianRestriction f).PreservesInjectiveObjects]
        [(etaleAbelianRestriction f ⋙
          siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
        (q : ℕ),
        pullbackH Y f q =
          etaleCohomologyRestrict f (extensionByZeroZModModule j G) q) :
    StatementsHold X (extensionByZeroZModModule j G)
      (fun Y f ↦ (etaleAbelianRestriction f).obj) finiteLocallyConstant pullbackH := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
