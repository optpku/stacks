module

public import stacks_project.Chap59.Lemma_59_83_7
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)] [IsReduced X.left]
variable (ell : ℕ) [Fact (Nat.Prime ell)]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]

/-- Lemma 59.83.8: in Situation 59.83.1, if `X` is reduced, `j : U ⟶ X` is an open
immersion, and `ell` is prime, then statements (1)–(8) hold for
`F = j_! underline(ZMod ell)`, encoded as `StatementsHold` for
`extensionByZeroConstantZMod j ell`. -/
@[stacks 0A3Q]
public theorem statementsHold_of_isReduced_extensionByZeroConstantZMod
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
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
        etaleCohomology X.left (extensionByZeroConstantZMod j ell) q ⟶
          etaleCohomology Y
            ((etaleAbelianRestriction f).obj (extensionByZeroConstantZMod j ell)) q)
    (h_finite : ∀ (Y : Scheme.{u}) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
      finiteLocallyConstant Y G ↔ IsFiniteLocallyConstantAddCommGrp G)
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
          etaleCohomologyRestrict f (extensionByZeroConstantZMod j ell) q) :
    StatementsHold X (extensionByZeroConstantZMod j ell)
      (fun Y f ↦ (etaleAbelianRestriction f).obj) finiteLocallyConstant pullbackH := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
