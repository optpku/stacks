module

public import stacks_project.Chap59.Definition_59_71_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Topology

universe u v w

namespace CategoryTheory.Sheaf

/- Lemma 59.71.2 (1): for a quasi-compact and quasi-separated scheme, constructibility of a
set-valued étale sheaf is equivalent to constructibility after restriction to an open cover and to
a finite partition by constructible locally closed subschemes with finite locally constant
restrictions. -/
@[stacks 095E]
#check (CategoryTheory.Sheaf.isConstructibleEtaleSet_tfae :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))), List.TFAE [
      IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) F,
      ∃ (𝒰 : X.OpenCover), ∀ i : 𝒰.I₀,
        IsConstructibleEtaleSet
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
              (𝒰.X i).smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstant G)
          (((Scheme.smallEtalePullback (𝒰.f i)).sheafPullback (Type (u + 1))
            X.smallEtaleTopology (𝒰.X i).smallEtaleTopology).obj F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧ ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set X) ∧
          let T : LocallyCloseds X :=
            ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
          IsFiniteLocallyConstant
            (((Scheme.smallEtalePullback (Scheme.LocallyClosedReduction.ι T)).sheafPullback
              (Type (u + 1)) X.smallEtaleTopology
                (Scheme.LocallyClosedReduction.scheme T).smallEtaleTopology).obj F)])

/- Lemma 59.71.2 (2): the analogous equivalence holds for étale sheaves of abelian groups, with
finite locally constant restrictions. -/
@[stacks 095E]
#check (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_tfae :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), List.TFAE [
      IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F,
      ∃ (𝒰 : X.OpenCover), ∀ i : 𝒰.I₀,
        IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
              (𝒰.X i).smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G)
          (((Scheme.smallEtalePullback (𝒰.f i)).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology (𝒰.X i).smallEtaleTopology).obj F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧ ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set X) ∧
          let T : LocallyCloseds X :=
            ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
          IsFiniteLocallyConstantAddCommGrp
            (((Scheme.smallEtalePullback (Scheme.LocallyClosedReduction.ι T)).sheafPullback
              (AddCommGrpCat.{u + 1}) X.smallEtaleTopology
                (Scheme.LocallyClosedReduction.scheme T).smallEtaleTopology).obj F)])

/- Lemma 59.71.2 (3): for a Noetherian ring `Λ`, the analogous equivalence holds for étale
sheaves of `Λ`-modules, with locally constant finite-type restrictions. -/
@[stacks 095E]
#check (CategoryTheory.Sheaf.isConstructibleEtaleModule_tfae :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
    [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
      (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)), List.TFAE [
      IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
          IsFiniteTypeLocallyConstantModule G) F,
      ∃ (𝒰 : X.OpenCover), ∀ i : 𝒰.I₀,
        IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              (𝒰.X i).smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
            IsFiniteTypeLocallyConstantModule G)
          (((Scheme.smallEtalePullback (𝒰.f i)).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology (𝒰.X i).smallEtaleTopology).obj F),
      ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧ ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set X) ∧
          let T : LocallyCloseds X :=
            ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
          IsFiniteTypeLocallyConstantModule
            (((Scheme.smallEtalePullback (Scheme.LocallyClosedReduction.ι T)).sheafPullback
              (ModuleCat.{w} Λ) X.smallEtaleTopology
                (Scheme.LocallyClosedReduction.scheme T).smallEtaleTopology).obj F)])

end CategoryTheory.Sheaf
