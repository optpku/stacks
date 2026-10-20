/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProperSmoothCurve
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `(etaleModulePushforward f Λ).rightDerived`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

open AlgebraicGeometry.Scheme.Etale

/- Lemma 63.13.3: if `f : X ⟶ S` is a proper smooth morphism of schemes with
geometrically connected fibres of dimension `1`, `Λ` is a Noetherian ring, and
`M` is a finite `Λ`-module annihilated by an integer `n > 0`, then each higher
direct image of the constant sheaf of `M` is a constructible sheaf of `Λ`-modules
on the small étale site of `S`. -/
@[stacks 0GKW]
#check (AlgebraicGeometry.Scheme.Etale.higherDirectImage_constantModule_isConstructible :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {M : Type u} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    (n : ℕ) (hn : 0 < n) (hM : Module.IsTorsionBy Λ M (n : Λ)) (q : ℕ)
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
    [EnoughInjectives (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [(etaleModulePushforward f Λ).Additive]
    [∀ (Y : Scheme.{u}) (g : Y ⟶ S) (G : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
      (smallEtalePullback g).op.HasLeftKanExtension G],
    IsConstructibleEtaleModule
      (fun {Y} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          S.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G)
      (((etaleModulePushforward f Λ).rightDerived q).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (.of Λ M))))

end
