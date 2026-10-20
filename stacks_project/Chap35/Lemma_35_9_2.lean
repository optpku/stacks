module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Cech.Amitsur
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open SheafOfModules.RingedSite.Cech

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/- Lemma 35.9.2 (1): for a standard affine cover in any of the five big standard
topologies, restriction from the covered affine scheme to the coproduct is faithfully flat. -/
@[stacks 03FJ]
#check
  (AlgebraicGeometry.StandardTopology.coproductSectionsMap_faithfullyFlat :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (U : Over S) (n : ℕ)
      (𝒰 : Fin n → Over U)
      (h_affine : ∀ i, IsAffine ((Over.forget S).obj (𝒰 i).left))
      (h_cover : τ.IsCover
        (AffineFamilyOver.ofSiteFamily (Over.forget S) U n 𝒰 h_affine))
      [HasCoproduct (fun i ↦ (𝒰 i).left)],
      RingHom.FaithfullyFlat
        (coproductSectionsMap ((Over.forget S).op ⋙ Scheme.Γ) U 𝒰))

/- Lemma 35.9.2 (2): the Čech complex of a standard affine cover on any big standard
site is isomorphic to the Amitsur complex of its coproduct sections map. -/
@[stacks 03FJ]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigCech_isIsomorphic_amitsur :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
      (U : Over S) (n : ℕ) (𝒰 : Fin n → Over U)
      (h_affine : ∀ i, IsAffine ((Over.forget S).obj (𝒰 i).left))
      (h_cover : τ.IsCover
        (AffineFamilyOver.ofSiteFamily (Over.forget S) U n 𝒰 h_affine))
      [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)],
      IsIsomorphic
        ((SheafOfModules.RingedSite.cechComplex
          (bigStructureSheaf τ S) U
            (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)).obj (big τ S F).val)
        (amitsurComplex ((Over.forget S).op ⋙ Scheme.Γ) U 𝒰 (big τ S F).val))

/- Lemma 35.9.2 (3): positive Čech cohomology of an associated quasi-coherent module
vanishes for a standard affine cover on any big standard site. -/
@[stacks 03FJ]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigCechCohomology_isZero :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
      (U : Over S) (n : ℕ) (𝒰 : Fin n → Over U)
      (h_affine : ∀ i, IsAffine ((Over.forget S).obj (𝒰 i).left))
      (h_cover : τ.IsCover
        (AffineFamilyOver.ofSiteFamily (Over.forget S) U n 𝒰 h_affine))
      [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)] (p : ℕ),
      IsZero (SheafOfModules.RingedSite.cechCohomology
        (bigStructureSheaf τ S) U (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)
          (big τ S F).val (p + 1)))

/- Lemma 35.9.2 (4): for a standard affine cover on the small Zariski or étale site,
restriction from the covered affine scheme to the coproduct is faithfully flat. -/
@[stacks 03FJ]
#check
  (AlgebraicGeometry.SmallStandardTopology.coproductSectionsMap_faithfullyFlat :
    ∀ (σ : SmallStandardTopology) (S : Scheme.{u}) (U : σ.site S)
      (n : ℕ) (𝒰 : Fin n → Over U)
      (h_affine : ∀ i, IsAffine ((σ.toScheme S).obj (𝒰 i).left))
      (h_cover : σ.toStandard.IsCover
        (AffineFamilyOver.ofSiteFamily (σ.toScheme S) U n 𝒰 h_affine))
      [HasCoproduct (fun i ↦ (𝒰 i).left)],
      RingHom.FaithfullyFlat
        (coproductSectionsMap ((σ.toScheme S).op ⋙ Scheme.Γ) U 𝒰))

/- Lemma 35.9.2 (5): the Čech complex of a standard affine cover on the small Zariski
or étale site is isomorphic to the Amitsur complex of its coproduct sections map. -/
@[stacks 03FJ]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallCech_isIsomorphic_amitsur :
    ∀ (σ : SmallStandardTopology) (S : Scheme.{u})
      (F : S.Modules) [F.IsQuasicoherent] (U : σ.site S)
      (n : ℕ) (𝒰 : Fin n → Over U)
      (h_affine : ∀ i, IsAffine ((σ.toScheme S).obj (𝒰 i).left))
      (h_cover : σ.toStandard.IsCover
        (AffineFamilyOver.ofSiteFamily (σ.toScheme S) U n 𝒰 h_affine))
      [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)],
      IsIsomorphic
        ((SheafOfModules.RingedSite.cechComplex
          (smallStructureSheaf σ S) U
            (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)).obj (small σ S F).val)
        (amitsurComplex ((σ.toScheme S).op ⋙ Scheme.Γ) U 𝒰 (small σ S F).val))

/- Lemma 35.9.2 (6): positive Čech cohomology of an associated quasi-coherent module
vanishes for a standard affine cover on the small Zariski or étale site. -/
@[stacks 03FJ]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallCechCohomology_isZero :
    ∀ (σ : SmallStandardTopology) (S : Scheme.{u})
      (F : S.Modules) [F.IsQuasicoherent] (U : σ.site S)
      (n : ℕ) (𝒰 : Fin n → Over U)
      (h_affine : ∀ i, IsAffine ((σ.toScheme S).obj (𝒰 i).left))
      (h_cover : σ.toStandard.IsCover
        (AffineFamilyOver.ofSiteFamily (σ.toScheme S) U n 𝒰 h_affine))
      [HasFiniteProducts (Over U)] [HasCoproduct (fun i ↦ (𝒰 i).left)] (p : ℕ),
      IsZero (SheafOfModules.RingedSite.cechCohomology
        (smallStructureSheaf σ S) U (fun i : ULift.{u} (Fin n) ↦ 𝒰 i.down)
          (small σ S F).val (p + 1)))

end AlgebraicGeometry.Scheme.AssociatedModule
