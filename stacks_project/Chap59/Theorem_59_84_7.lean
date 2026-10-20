/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.ConstructibleModule
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GrothendieckTopology

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/- Theorem 59.84.7 (1): constructible torsion sheaves of modules over a Noetherian ring on a
separated finite-type curve over an algebraically closed field have finitely generated étale
cohomology when the torsion is prime to the characteristic. -/
@[stacks 0GJI] #check (AlgebraicGeometry.Scheme.Etale.etaleCohomology_finite_of_constructible_primeToChar :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
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
        (forget₂ (ModuleCat.{max u (v + 1)} Λ) AddCommGrpCat)).obj F)) (q : ℕ),
    Module.Finite Λ ((siteModuleCohomologyModuleFunctor q).obj F))

/- Theorem 59.84.7 (2): constructible torsion sheaves of modules over a Noetherian ring on a
proper curve over an algebraically closed field have finitely generated étale cohomology. -/
@[stacks 0GJI] #check (AlgebraicGeometry.Scheme.Etale.etaleCohomology_finite_of_isProper_constructible :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
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
    (q : ℕ),
    Module.Finite Λ ((siteModuleCohomologyModuleFunctor q).obj F))

end AlgebraicGeometry.Scheme.Etale
