module

public import ReasLib.Algebra.Amitsur.Acyclic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cech.Amitsur
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Cech.CoproductSingleton

/-!
# Čech–Amitsur comparison for associated modules

This module compares the Čech complexes of finite standard affine covers with
the corresponding Amitsur complexes and records positive-degree vanishing.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open SheafOfModules.RingedSite.Cech

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The Čech complex of a standard affine cover on any big standard site is isomorphic to
the Amitsur complex of its coproduct sections map. -/
theorem bigCech_isIsomorphic_amitsur
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : Over S) (n : ℕ) (𝒰 : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((Over.forget S).obj (𝒰 i).left))
    (h_cover : τ.IsCover
      (AffineFamilyOver.ofSiteFamily (Over.forget S) U n 𝒰 h_affine))
    [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)] :
    IsIsomorphic
      ((SheafOfModules.RingedSite.cechComplex
        (bigStructureSheaf τ S) U
          (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)).obj (big τ S F).val)
      (amitsurComplex ((Over.forget S).op ⋙ Scheme.Γ) U 𝒰 (big τ S F).val) := sorry

/-- Positive Čech cohomology of an associated quasi-coherent module vanishes for a standard
affine cover on any big standard site. -/
theorem bigCechCohomology_isZero
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : Over S) (n : ℕ) (𝒰 : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((Over.forget S).obj (𝒰 i).left))
    (h_cover : τ.IsCover
      (AffineFamilyOver.ofSiteFamily (Over.forget S) U n 𝒰 h_affine))
    [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)] (p : ℕ) :
    IsZero (SheafOfModules.RingedSite.cechCohomology
      (bigStructureSheaf τ S) U (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)
        (big τ S F).val (p + 1)) := sorry

/-- The Čech complex of a standard affine cover on the small Zariski or small étale site is
isomorphic to the Amitsur complex of its coproduct sections map. -/
theorem smallCech_isIsomorphic_amitsur
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] (U : σ.site S)
    (n : ℕ) (𝒰 : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((σ.toScheme S).obj (𝒰 i).left))
    (h_cover : σ.toStandard.IsCover
      (AffineFamilyOver.ofSiteFamily (σ.toScheme S) U n 𝒰 h_affine))
    [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)] :
    IsIsomorphic
      ((SheafOfModules.RingedSite.cechComplex
        (smallStructureSheaf σ S) U
          (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)).obj (small σ S F).val)
      (amitsurComplex ((σ.toScheme S).op ⋙ Scheme.Γ) U 𝒰 (small σ S F).val) := sorry

/-- Positive Čech cohomology of an associated quasi-coherent module vanishes for a standard
affine cover on the small Zariski or small étale site. -/
theorem smallCechCohomology_isZero
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] (U : σ.site S)
    (n : ℕ) (𝒰 : Fin n → Over U)
    (h_affine : ∀ i, IsAffine ((σ.toScheme S).obj (𝒰 i).left))
    (h_cover : σ.toStandard.IsCover
      (AffineFamilyOver.ofSiteFamily (σ.toScheme S) U n 𝒰 h_affine))
    [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)] (p : ℕ) :
    IsZero (SheafOfModules.RingedSite.cechCohomology
      (smallStructureSheaf σ S) U (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)
        (small σ S F).val (p + 1)) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
