/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

/- Lemma 59.84.5: for a Noetherian ring `Λ`, an algebraically closed field `k`,
and a separated finite-type `k`-scheme `X` of dimension at most one, finiteness of
the degree-`q` étale cohomology of the two endpoint sheaves in a short exact
sequence implies finiteness of the degree-`q` étale cohomology of the middle
sheaf. -/
@[stacks 0GJG] #check
  (AlgebraicGeometry.Scheme.Etale.finiteCohomologyOfShortExact :
    ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      {k : Type v} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
      (h_dimension : topologicalKrullDim X.left ≤ 1)
      (q : ℕ)
      {F₁ F F₂ : Sheaf X.left.smallEtaleTopology
        (ModuleCat.{max u (v + 1)} Λ)}
      (i : F₁ ⟶ F) (p : F ⟶ F₂) (h_ip : i ≫ p = 0)
      (h_sheaf : (ShortComplex.mk i p h_ip).ShortExact)
      [HasWeakSheafify X.left.smallEtaleTopology
        (ModuleCat.{max u (v + 1)} Λ)]
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
      [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
      [X.left.smallEtaleTopology.HasSheafCompose
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
      [Module.Finite Λ
        ((siteModuleCohomologyModuleFunctor
          (J := X.left.smallEtaleTopology) (A := Λ) q).obj F₁)]
      [Module.Finite Λ
        ((siteModuleCohomologyModuleFunctor
          (J := X.left.smallEtaleTopology) (A := Λ) q).obj F₂)],
      Module.Finite Λ
        ((siteModuleCohomologyModuleFunctor
          (J := X.left.smallEtaleTopology) (A := Λ) q).obj F))

end
