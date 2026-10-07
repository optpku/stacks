module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap59.Lemma_59_83_4_Statements

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Etale.TorsionOnCurve

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X Y : SchemeOverField k)
variable [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType Y.hom]
variable [IsSeparated X.hom] [IsSeparated Y.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)]
variable [Fact (topologicalKrullDim Y.left ≤ 1)]
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]
variable [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal Y.left.Etale]
variable [(siteAbelianSectionsFunctor Y.left.smallEtaleTopology (terminal Y.left.Etale)).Additive]
variable (f : X.left ⟶ Y.left) [IsFinite f]
variable (restrictX :
    (Z : Scheme.{u}) → (Z ⟶ X.left) →
      Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u} →
        Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
variable (finiteLocallyConstantX :
    (Z : Scheme.{u}) → Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} → Prop)
variable (pullbackHX :
    (Z : Scheme.{u}) → (g : Z ⟶ X.left) →
      [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}] →
      [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})] →
      [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})] →
      [HasTerminal Z.Etale] →
      [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive] →
      (q : ℕ) →
      etaleCohomology X.left F q ⟶ etaleCohomology Z (restrictX Z g F) q)
variable (restrictY :
    (Z : Scheme.{u}) → (Z ⟶ Y.left) →
      Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u} →
        Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
variable (finiteLocallyConstantY :
    (Z : Scheme.{u}) → Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} → Prop)
variable (pullbackHY :
    (Z : Scheme.{u}) → (g : Z ⟶ Y.left) →
      [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}] →
      [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})] →
      [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})] →
      [HasTerminal Z.Etale] →
      [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive] →
      (q : ℕ) →
      etaleCohomology Y.left ((etaleAbelianPushforward f).obj F) q ⟶
        etaleCohomology Z (restrictY Z g ((etaleAbelianPushforward f).obj F)) q)

/-- Lemma 59.83.5: if `k` is algebraically closed and `f : X ⟶ Y` is a finite morphism of
separated finite-type schemes over `k` of dimension `≤ 1`, and if statements (1)–(8) of
Situation 59.83.1 hold for a torsion abelian étale sheaf `F` on `X` (as
`StatementsHold`), then they hold for `f_* F`, encoded as
`StatementsHold` for `(etaleAbelianPushforward f).obj F` on `Y`. -/
@[stacks 0A5D]
theorem StatementsHold.of_finite_pushforward
    (h_over : f ≫ Y.hom = X.hom)
    [StatementsHold X F restrictX finiteLocallyConstantX pullbackHX] :
    StatementsHold Y ((etaleAbelianPushforward f).obj F) restrictY
      finiteLocallyConstantY pullbackHY := sorry
