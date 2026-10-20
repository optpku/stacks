/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale.CurveCohomology.LocallyConstantModule

/-- For a Noetherian ring `Λ`, an algebraically closed field `k`, a
separated finite-type `k`-scheme `X` of dimension at most one, an open immersion
`j : U ⟶ X.left` with `U` connected, a prime `ℓ`, an integer `n > 0`, and a finite-type
locally constant sheaf `G` of `Λ`-modules on `U.smallEtaleTopology` annihilated by
`ℓ ^ n`, the étale cohomology of `j_! G` is a finite `Λ`-module whenever `ℓ` is a unit
in `k`. -/
@[stacks 0GJH]
theorem finite_extensionByZero_of_primeToChar
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
    (h_ann : (ℓ ^ n : ℕ) • 𝟙 G = 0) (hℓk : IsUnit (ℓ : k)) (q : ℕ) :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor q).obj
        ((etaleExtensionByZero j (ModuleCat.{max u (v + 1)} Λ)).obj G)) := sorry

/-- For a Noetherian ring `Λ`, an algebraically closed field `k`, a
separated finite-type `k`-scheme `X` of dimension at most one, an open immersion
`j : U ⟶ X.left` with `U` connected, a prime `ℓ`, an integer `n > 0`, and a finite-type
locally constant sheaf `G` of `Λ`-modules on `U.smallEtaleTopology` annihilated by
`ℓ ^ n`, the étale cohomology of `j_! G` is a finite `Λ`-module whenever `X` is proper
over `k`. -/
@[stacks 0GJH]
theorem finite_extensionByZero_of_isProper
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
    (h_ann : (ℓ ^ n : ℕ) • 𝟙 G = 0) (q : ℕ) :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor q).obj
        ((etaleExtensionByZero j (ModuleCat.{max u (v + 1)} Λ)).obj G)) := sorry

end AlgebraicGeometry.Scheme.Etale.CurveCohomology.LocallyConstantModule
