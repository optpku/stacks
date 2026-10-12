/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u w

namespace CategoryTheory.Sheaf

/- Lemma 59.73.6 (1): constructible étale module sheaves are precisely the cokernels of maps
between finite sums of regular constant sheaves extended by zero from quasi-compact and
quasi-separated étale objects. -/
@[stacks 095N]
#check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_iff_exists_cokernel :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      [HasFiniteCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
      [∀ (n : ℕ) (F : Fin n → Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
        HasCoproduct F]
      [HasCokernels (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
      (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
      IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F ↔
        ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
          (∀ i, CompactSpace (U i).left) ∧
            (∀ i, QuasiSeparatedSpace (U i).left) ∧
              (∀ k, CompactSpace (V k).left) ∧
                (∀ k, QuasiSeparatedSpace (V k).left) ∧
                  ∃ (φ :
                      finiteExtensionByZeroSum (h := fun k ↦ (V k).prop)
                          (hKan := fun k P ↦ hExtension (V k) P)
                          (fun k ↦ (V k).left) (fun k ↦ (V k).hom) ⟶
                      finiteExtensionByZeroSum (h := fun i ↦ (U i).prop)
                          (hKan := fun i P ↦ hExtension (U i) P)
                          (fun i ↦ (U i).left) (fun i ↦ (U i).hom)),
                    Nonempty (F ≅ cokernel φ))

/- Lemma 59.73.6 (2): the same finite-cokernel characterization holds with affine étale
objects. -/
@[stacks 095N]
#check
  (CategoryTheory.Sheaf.isConstructibleEtaleModule_iff_exists_cokernel_affine :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
      [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      [HasFiniteCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
      [∀ (n : ℕ) (F : Fin n → Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
        HasCoproduct F]
      [HasCokernels (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
      (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
        (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
      IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F ↔
        ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
          (∀ i, IsAffine (U i).left) ∧
            (∀ k, IsAffine (V k).left) ∧
              ∃ (φ :
                  finiteExtensionByZeroSum (h := fun k ↦ (V k).prop)
                      (hKan := fun k P ↦ hExtension (V k) P)
                      (fun k ↦ (V k).left) (fun k ↦ (V k).hom) ⟶
                  finiteExtensionByZeroSum (h := fun i ↦ (U i).prop)
                      (hKan := fun i P ↦ hExtension (U i) P)
                      (fun i ↦ (U i).left) (fun i ↦ (U i).hom)),
                Nonempty (F ≅ cokernel φ))

end CategoryTheory.Sheaf
