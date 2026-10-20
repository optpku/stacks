/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.LocallyConstantModule
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.84.6 (1): finiteness of étale cohomology with locally constant coefficients. -/
@[stacks 0GJH] #check (AlgebraicGeometry.Scheme.Etale.CurveCohomology.LocallyConstantModule.finite_extensionByZero_of_primeToChar :
    ∀
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    {U : Scheme.{v}} (j : U ⟶ X.left) [IsOpenImmersion j] [ConnectedSpace U]
    (ℓ n : ℕ) [Fact (Nat.Prime ℓ)] (hn : 0 < n)
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V)
      (ModuleCat.{max u (v + 1)} Λ)]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{max u (v + 1)} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    [Sheaf.IsLocallyConstantWith (fun M : ModuleCat.{max u (v + 1)} Λ ↦ Module.Finite Λ M) G]
    (h_ann : (ℓ ^ n : ℕ) • 𝟙 G = 0) (hℓk : IsUnit (ℓ : k)) (q : ℕ),
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor q).obj
        ((etaleExtensionByZero j (ModuleCat.{max u (v + 1)} Λ)).obj G)))

/- Lemma 59.84.6 (2): finiteness of étale cohomology with locally constant coefficients. -/
@[stacks 0GJH] #check (AlgebraicGeometry.Scheme.Etale.CurveCohomology.LocallyConstantModule.finite_extensionByZero_of_isProper :
    ∀
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    [IsProper X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    {U : Scheme.{v}} (j : U ⟶ X.left) [IsOpenImmersion j] [ConnectedSpace U]
    (ℓ n : ℕ) [Fact (Nat.Prime ℓ)] (hn : 0 < n)
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V)
      (ModuleCat.{max u (v + 1)} Λ)]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{max u (v + 1)} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    [Sheaf.IsLocallyConstantWith (fun M : ModuleCat.{max u (v + 1)} Λ ↦ Module.Finite Λ M) G]
    (h_ann : (ℓ ^ n : ℕ) • 𝟙 G = 0) (q : ℕ),
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor q).obj
        ((etaleExtensionByZero j (ModuleCat.{max u (v + 1)} Λ)).obj G)))

end AlgebraicGeometry.Scheme.Etale
