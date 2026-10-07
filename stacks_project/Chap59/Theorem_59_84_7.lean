module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_71_1

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

/-- A sheaf of `Λ`-modules is of torsion prime to `char(k)` when every section is annihilated
by a positive integer that is a unit in `k`. -/
def IsPrimeToCharTorsionModule {C : Type (v + 1)} [Category.{v} C]
    {J : GrothendieckTopology C} (k : Type v) [Field k] {Λ : Type u} [CommRing Λ]
    (F : Sheaf J (ModuleCat.{max u (v + 1)} Λ)) : Prop :=
  ∀ (U : C) (s : F.obj.obj (op U)),
    ∃ n : ℕ, 0 < n ∧ (n : Λ) • s = 0 ∧ IsUnit (n : k)

/-- Unfolding of prime-to-characteristic torsion for sheaves of modules. -/
theorem isPrimeToCharTorsionModule_iff {C : Type (v + 1)} [Category.{v} C]
    {J : GrothendieckTopology C} (k : Type v) [Field k] {Λ : Type u} [CommRing Λ]
    (F : Sheaf J (ModuleCat.{max u (v + 1)} Λ)) :
    IsPrimeToCharTorsionModule k F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ n : ℕ, 0 < n ∧ (n : Λ) • s = 0 ∧ IsUnit (n : k) := sorry

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

/-- Inverse image of a sheaf of `Λ`-modules along a morphism of schemes on small étale sites. -/
noncomputable abbrev etaleModuleRestriction {X Y : Scheme.{v}} (f : Y ⟶ X) {Λ : Type u}
    [CommRing Λ]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{max u (v + 1)} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint] :
    Sheaf X.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ) :=
  (smallEtalePullback f).sheafPullback (ModuleCat.{max u (v + 1)} Λ)
    X.smallEtaleTopology Y.smallEtaleTopology

/-- Evaluating `etaleModuleRestriction` recovers sheaf pullback along `smallEtalePullback`. -/
theorem etaleModuleRestriction_eq {X Y : Scheme.{v}} (f : Y ⟶ X) {Λ : Type u} [CommRing Λ]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{max u (v + 1)} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint] :
    etaleModuleRestriction f =
      (smallEtalePullback f).sheafPullback (ModuleCat.{max u (v + 1)} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Etale

/-- Theorem 59.84.7 (1): for a Noetherian ring `Λ`, an algebraically closed field `k`, a
separated finite-type `k`-scheme `X` of dimension at most one, and a constructible torsion
sheaf `F` of `Λ`-modules on `X.smallEtaleTopology`, the étale cohomology of `F` is a finite
`Λ`-module whenever `F` is of torsion prime to `char(k)`. -/
@[stacks 0GJI]
theorem etaleCohomology_finite_of_constructible_primeToChar
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    [∀ Y : Scheme.{v}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (f : Y ⟶ X.left),
      ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{max u (v + 1)} Λ)
          X.left.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    (h_cons : Sheaf.IsConstructibleEtale
      (fun {Y} f ↦ (etaleModuleRestriction f).obj)
      (fun {Y} G ↦ Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{max u (v + 1)} Λ ↦ Module.Finite Λ M) G) F)
    (h_torsion : Sheaf.IsLocallyTorsion
      ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)).obj F))
    (h_prime : Sheaf.IsPrimeToCharTorsionModule k F) (q : ℕ) :
    Module.Finite Λ ((siteModuleCohomologyModuleFunctor q).obj F) := sorry

/-- Theorem 59.84.7 (2): for a Noetherian ring `Λ`, an algebraically closed field `k`, a
separated finite-type `k`-scheme `X` of dimension at most one, and a constructible torsion
sheaf `F` of `Λ`-modules on `X.smallEtaleTopology`, the étale cohomology of `F` is a finite
`Λ`-module whenever `X` is proper over `k`. -/
@[stacks 0GJI]
theorem etaleCohomology_finite_of_isProper_constructible
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {k : Type v} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    [IsProper X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    [∀ Y : Scheme.{v}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{max u (v + 1)} Λ)]
    [∀ (Y : Scheme.{v}) (f : Y ⟶ X.left),
      ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{max u (v + 1)} Λ)
          X.left.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)}]
    [HasExt (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max u (v + 1)})]
    [HasSheafCompose X.left.smallEtaleTopology
      (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{max u (v + 1)} Λ))
    (h_cons : Sheaf.IsConstructibleEtale
      (fun {Y} f ↦ (etaleModuleRestriction f).obj)
      (fun {Y} G ↦ Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{max u (v + 1)} Λ ↦ Module.Finite Λ M) G) F)
    (h_torsion : Sheaf.IsLocallyTorsion
      ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)).obj F))
    (q : ℕ) :
    Module.Finite Λ ((siteModuleCohomologyModuleFunctor q).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale

