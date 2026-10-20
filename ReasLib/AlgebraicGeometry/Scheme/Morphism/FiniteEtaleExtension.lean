module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.FiniteEtaleExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Properties
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open RingedSpace
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The pushforward algebra of a finite étale cover along an open immersion of locally
Noetherian schemes with depth at least two on the complement is reflexive and coherent. -/
theorem finiteEtaleExtension_reflexive_coherent
    {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    let B := finiteEtaleExtensionAlgebra j π hdepth
    Scheme.Modules.IsReflexive (QcAlgebraUnder.underlyingModule X B) ∧
      (QcAlgebraUnder.underlyingModule X B).IsCoherent := sorry

/-- The relative spectrum of the extension algebra is finite over the base, restricts to
the original cover, has depth at least two on the complement, and is uniquely characterized
by these properties together with its restriction isomorphism. -/
theorem finiteEtaleExtension_realization
    {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
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
                    candidateRestrictIso.hom → e' = e := sorry

/-- A finite realization of the extension algebra is étale at a point if and only if
it is flat at that point. -/
theorem finiteEtaleExtension_etaleAt_iff_flatAt
    {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (R : RelativeSpectrumRealization (finiteEtaleExtensionAlgebra j π hdepth))
    (hfinite : IsFinite R.toBase) :
    let f := R.toBase
    let sh := f.toLRSHom.toShHom
    ∀ y : R.Y, f.EtaleAt y ↔ RingedSpace.Hom.FlatAt sh y := sorry

/-- A finite realization of the extension algebra is étale if and only if the underlying
algebra module is finite locally free. -/
theorem finiteEtaleExtension_etale_iff_finiteLocallyFree
    {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (R : RelativeSpectrumRealization (finiteEtaleExtensionAlgebra j π hdepth))
    (hfinite : IsFinite R.toBase) :
    Etale R.toBase ↔
      Scheme.Modules.IsFiniteLocallyFree
        (QcAlgebraUnder.underlyingModule X (finiteEtaleExtensionAlgebra j π hdepth)) := sorry

/-- The extension algebra of a finite étale cover and its relative-spectrum realizations
commute with flat base change between locally Noetherian schemes. -/
theorem finiteEtaleExtension_baseChange
    {U X V X' : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (g : X' ⟶ X) [IsLocallyNoetherian X'] [Flat g] :
    let B := finiteEtaleExtensionAlgebra j π hdepth
    let j' := pullback.fst g j
    let π' := pullback.snd π (pullback.snd g j)
    ∃ hdepth' : ∀ x : X', x ∉ Set.range j'.base →
      (2 : ℕ∞) ≤ moduleDepth (X'.presheaf.stalk x) (X'.presheaf.stalk x),
      let B' := finiteEtaleExtensionAlgebra j' π' hdepth'
      ∃ pullbackData : RelativeSpectrumPullback g B B',
        ∀ R : RelativeSpectrumRealization B,
          ∀ R' : RelativeSpectrumRealization B',
            Nonempty (Over.mk (pullback.snd R.toBase g) ≅ Over.mk R'.toBase) := sorry

/-- An extension of a finite étale cover to a larger open is uniquely isomorphic to the
restriction of the finite relative-spectrum extension, compatibly with the given
identification over the original open. -/
theorem finiteEtaleExtension_largerOpen
    {U U' X V V' : Scheme.{u}} (j : U ⟶ X) (j' : U' ⟶ X) (i : U ⟶ U')
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
    (hfinite : IsFinite R.toBase) :
    ∃ e : Over.mk (pullback.snd R.toBase j') ≅ Over.mk π',
      (Over.pullback i).map e.hom ≫ restrictIso.hom = realizationRestrictIso.hom ∧
        ∀ e' : Over.mk (pullback.snd R.toBase j') ≅ Over.mk π',
          (Over.pullback i).map e'.hom ≫ restrictIso.hom =
            realizationRestrictIso.hom → e' = e := sorry

end AlgebraicGeometry.Scheme.Hom
