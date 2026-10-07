module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 59.84.1 (1): for a Noetherian ring `Λ`, a finite `Λ`-module `M` annihilated by an
integer `n > 0`, an algebraically closed field `k`, and a separated finite-type `k`-scheme
`X` of dimension at most one, the étale cohomology of the constant sheaf of `M` is a finite
`Λ`-module whenever `n` is a unit in `k`. -/
@[stacks 0GJC]
theorem etaleCohomology_constant_finite_of_primeToChar
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {M : Type (max u (v + 1))} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    (n : ℕ) (hn : 0 < n) (hM : Module.IsTorsionBy Λ M (n : Λ))
    (hnk : IsUnit (n : k)) (q : ℕ)
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)] :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor q).obj
        ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)).obj
          (.of Λ M))) := sorry

/-- Lemma 59.84.1 (2): for a Noetherian ring `Λ`, a finite `Λ`-module `M` annihilated by an
integer `n > 0`, an algebraically closed field `k`, and a separated finite-type `k`-scheme
`X` of dimension at most one, the étale cohomology of the constant sheaf of `M` is a finite
`Λ`-module whenever `X` is proper over `k`. -/
@[stacks 0GJC]
theorem etaleCohomology_constant_finite_of_isProper
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {M : Type (max u (v + 1))} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    [IsProper X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    (n : ℕ) (hn : 0 < n) (hM : Module.IsTorsionBy Λ M (n : Λ))
    (q : ℕ)
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)] :
    Module.Finite Λ
      ((siteModuleCohomologyModuleFunctor q).obj
        ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)).obj
          (.of Λ M))) := sorry

end AlgebraicGeometry.Scheme.Etale
