/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FiniteEtaleExtension
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteEtaleExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open RingedSpace
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

/- Lemma 58.21.5 (1): for an open immersion `j : U ⟶ X` of locally Noetherian schemes
with depth at least two on the complement and a finite étale `π : V ⟶ U`, the
pushforward algebra is reflexive and coherent. -/
@[stacks 0EY6] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleExtension_reflexive_coherent :
    ∀ {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)),
    let B := finiteEtaleExtensionAlgebra j π hdepth
    Scheme.Modules.IsReflexive (QcAlgebraUnder.underlyingModule X B) ∧
      (QcAlgebraUnder.underlyingModule X B).IsCoherent)

/- Lemma 58.21.5 (2): the relative spectrum of the pushforward algebra has a finite
structure morphism, restricts to `π` over `U`, has depth at least two off that open,
and is unique up to the compatible relative-spectrum isomorphism. -/
@[stacks 0EY6] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleExtension_realization :
    ∀ {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)),
    let B := finiteEtaleExtensionAlgebra j π hdepth
    ∃ R : RelativeSpectrumRealization B,
      let Y := R.Y
      ∃ restrictIso : Over.mk (pullback.snd R.toBase j) ≅ Over.mk π,
        IsFinite R.toBase ∧
          (∀ y : Y, y ∉ Set.range (pullback.fst R.toBase j).base →
            (2 : ℕ∞) ≤ moduleDepth (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ∧
          ∀ (Y' : Scheme.{u}) (f' : Y' ⟶ X) [IsFinite f']
              (candidateRestrictIso : Over.mk (pullback.snd f' j) ≅ Over.mk π),
            (∀ y : Y', y ∉ Set.range (pullback.fst f' j).base →
              (2 : ℕ∞) ≤ moduleDepth (Y'.presheaf.stalk y) (Y'.presheaf.stalk y)) →
            ∃ e : Over.mk f' ≅ Over.mk R.toBase,
              (Over.pullback j).map e.hom ≫ restrictIso.hom = candidateRestrictIso.hom ∧
                ∀ e' : Over.mk f' ≅ Over.mk R.toBase,
                  (Over.pullback j).map e'.hom ≫ restrictIso.hom =
                    candidateRestrictIso.hom → e' = e)

/- Lemma 58.21.5 (3): for a finite relative-spectrum realization, étaleness at a
point is equivalent to stalkwise flatness at that point. -/
@[stacks 0EY6] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleExtension_etaleAt_iff_flatAt :
    ∀ {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (R : RelativeSpectrumRealization (finiteEtaleExtensionAlgebra j π hdepth))
    (hfinite : IsFinite R.toBase),
    let f := R.toBase
    let sh := f.toLRSHom.toShHom
    ∀ y : R.Y, f.EtaleAt y ↔ RingedSpace.Hom.FlatAt sh y)

/- Lemma 58.21.5 (4): for a finite realization, the structure morphism is étale
exactly when the associated algebra module is finite locally free. -/
@[stacks 0EY6] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleExtension_etale_iff_finiteLocallyFree :
    ∀ {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (R : RelativeSpectrumRealization (finiteEtaleExtensionAlgebra j π hdepth))
    (hfinite : IsFinite R.toBase),
    Etale R.toBase ↔
      Scheme.Modules.IsFiniteLocallyFree
        (QcAlgebraUnder.underlyingModule X (finiteEtaleExtensionAlgebra j π hdepth)))

/- Lemma 58.21.5 (5): the pushforward algebra and its relative spectrum are
compatible with flat base change of locally Noetherian schemes. -/
@[stacks 0EY6] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleExtension_baseChange :
    ∀ {U X V X' : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (g : X' ⟶ X) [IsLocallyNoetherian X'] [Flat g],
    let B := finiteEtaleExtensionAlgebra j π hdepth
    let j' := pullback.fst g j
    let π' := pullback.snd π (pullback.snd g j)
    ∃ hdepth' : ∀ x : X', x ∉ Set.range j'.base →
      (2 : ℕ∞) ≤ moduleDepth (X'.presheaf.stalk x) (X'.presheaf.stalk x),
      let B' := finiteEtaleExtensionAlgebra j' π' hdepth'
      ∃ pullbackData : RelativeSpectrumPullback g B B',
        ∀ R : RelativeSpectrumRealization B,
          ∀ R' : RelativeSpectrumRealization B',
            Nonempty (Over.mk (pullback.snd R.toBase g) ≅ Over.mk R'.toBase))

/- Lemma 58.21.5 (6): enlarging the open over which the finite étale cover is
given yields a unique compatible relative-spectrum extension after restriction. -/
@[stacks 0EY6] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleExtension_largerOpen :
    ∀ {U U' X V V' : Scheme.{u}} (j : U ⟶ X) (j' : U' ⟶ X) (i : U ⟶ U')
    (π : V ⟶ U) (π' : V' ⟶ U')
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian U']
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i]
    [IsFinite π] [Etale π] [IsFinite π'] [Etale π']
    (hcomp : i ≫ j' = j)
    (restrictIso : Over.mk (pullback.snd π' i) ≅ Over.mk π)
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (R : RelativeSpectrumRealization (finiteEtaleExtensionAlgebra j π hdepth))
    (realizationRestrictIso :
      Over.mk (pullback.snd (pullback.snd R.toBase j') i) ≅ Over.mk π)
    (hfinite : IsFinite R.toBase),
    ∃ e : Over.mk (pullback.snd R.toBase j') ≅ Over.mk π',
      (Over.pullback i).map e.hom ≫ restrictIso.hom = realizationRestrictIso.hom ∧
        ∀ e' : Over.mk (pullback.snd R.toBase j') ≅ Over.mk π',
          (Over.pullback i).map e'.hom ≫ restrictIso.hom =
            realizationRestrictIso.hom → e' = e)
