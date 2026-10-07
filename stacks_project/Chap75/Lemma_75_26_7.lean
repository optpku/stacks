module

import StacksCheckRecall
public import stacks_project.Chap75.Lemma_75_26_7_StructureSheaf

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 75.26.7 (1): if `f` is proper, flat, and of finite presentation, and every
field-valued fibre satisfies `k = Γ(X_k, 𝒪_{X_k})`, then the canonical map
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism. -/
@[stacks 0E6B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.structureSheafMap_isIso_of_fiberGlobalSections :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      fiberGlobalSectionsBijective f → IsIso (structureSheafMap f))

/- Lemma 75.26.7 (2): the canonical structure-sheaf pushforward map remains an
isomorphism after every base change. -/
@[stacks 0E6B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.baseChange_structureSheafMap_isIso_of_fiberGlobalSections :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      fiberGlobalSectionsBijective f →
        ∀ g : Y' ⟶ Y, IsIso (structureSheafMap (pullback.snd f g)))

/- Lemma 75.26.7 (3): étale locally on `Y`, `Rf_* 𝒪_X` is the biproduct of the
degree-zero structure sheaf and a perfect complex of Tor-amplitude in `[1, ∞)`. -/
@[stacks 0E6B] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_etale_structureSheafPushforward_decomposition :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      fiberGlobalSectionsBijective f → ∀ y : Points Y,
      ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y) (y' : Points Y'),
        AlgebraicSpace.Etale g ∧ Points.map g y' = y ∧
          ∃ P : ModuleDerived Y',
            ModuleDerived.IsPerfect P ∧ ModuleDerived.HasTorAmplitudeGE P 1 ∧
              IsIsomorphic ((ModuleDerived.pullback g).obj
                  (pushforwardStructureSheafDerived f))
                (structureSheafDerived Y' ⊞ P))
