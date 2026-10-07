module

public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.11.2 (Flat base change) (1): for a cartesian square of algebraic spaces over a
scheme `S`, with `g` flat and `f` quasi-compact and quasi-separated, and `ℱ` a quasi-coherent
`𝒪_X`-module, the Cohomology-on-Sites 21.15.1 base-change map
`g^* R^i f_* ℱ ⟶ R^i f'_* ((g')^* ℱ)` is an isomorphism for every `i ≥ 0`. -/
@[stacks 073K] #check
  (Modules.isIso_higherDirectImageBaseChangeHom :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (h_cart : IsPullback g' f' f g) [Flat g] [Flat g']
      [QuasiCompact f] [QuasiSeparated f]
      [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ),
      IsIso (Modules.higherDirectImageBaseChangeHom h_cart ℱ i))

/- Lemma 69.11.2 (Flat base change) (2): if in addition `Y = Spec A` and `Y' = Spec B` over
`S`, then `H^i(X, ℱ) ⊗_A B` identifies with `H^i(X', (g')^* ℱ)`. -/
@[stacks 073K] #check
  (Modules.isIso_cohomologyBaseChangeHom :
    ∀ {S : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [Module.Flat A B] {X X' : AlgebraicSpace S}
      (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
      (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
      (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
      (h_cart : IsPullback g' f' f
        (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
      [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
      [Flat g'] [QuasiCompact f] [QuasiSeparated f]
      [Abelian X.Modules] [Abelian X'.Modules]
      [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ),
      IsIso (Modules.cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i))
