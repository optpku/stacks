/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion.Primary
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- Over an algebraically closed field, a constructible torsion sheaf of modules over a
Noetherian ring on a separated finite-type scheme of dimension at most one has finitely
generated étale cohomology in every degree if its torsion is prime to the characteristic. -/
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
      (fun {Y} f ↦
        ((smallEtalePullback f).sheafPullback (ModuleCat.{max u (v + 1)} Λ)
          X.left.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{max u (v + 1)} Λ ↦ Module.Finite Λ M) G) F)
    (h_torsion : Sheaf.IsLocallyTorsion
      ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)).obj F))
    (h_prime : Sheaf.IsLocallyPrimeToCharTorsion k
      ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)).obj F)) (q : ℕ) :
    Module.Finite Λ ((siteModuleCohomologyModuleFunctor q).obj F) := sorry

/-- Over an algebraically closed field, a constructible torsion sheaf of modules over a
Noetherian ring on a proper scheme of dimension at most one has finitely generated étale
cohomology in every degree. -/
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
      (fun {Y} f ↦
        ((smallEtalePullback f).sheafPullback (ModuleCat.{max u (v + 1)} Λ)
          X.left.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{max u (v + 1)} Λ ↦ Module.Finite Λ M) G) F)
    (h_torsion : Sheaf.IsLocallyTorsion
      ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)).obj F))
    (q : ℕ) :
    Module.Finite Λ ((siteModuleCohomologyModuleFunctor q).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale
