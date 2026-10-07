module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

open PerfectDerived.TorNegOneZero.Determinant
open Scheme.Hom.NaiveCotangent.BaseChange

/-- The canonical map from the pullback of absolute differential forms along a scheme morphism
to absolute differential forms on its source. -/
noncomputable def absoluteFormComparison {X' X : Scheme.{u}} (g : X' ⟶ X) (p : ℕ) :
    (RingedSpace.Hom.pullback g.toShHom).obj
        (Λ[p] Ω[(terminal.from X).toShHom]) ⟶
      Λ[p] Ω[(terminal.from X').toShHom] :=
  formComparison
    (CommSq.mk (Subsingleton.elim
      (g ≫ terminal.from X) (terminal.from X' ≫ 𝟙 _))) p

/-- The absolute-form comparison is the relative-form comparison for the canonical square over
the terminal scheme. -/
theorem absoluteFormComparison_def {X' X : Scheme.{u}} (g : X' ⟶ X) (p : ℕ) :
    absoluteFormComparison g p =
      formComparison
        (CommSq.mk (Subsingleton.elim
          (g ≫ terminal.from X) (terminal.from X' ≫ 𝟙 _))) p := sorry

/-- The derived naive cotangent complex of a syntomic morphism is perfect. -/
theorem naiveCotangent_isPerfect_of_syntomic {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Syntomic f] :
    RingedSpace.ModuleDerived.IsPerfect
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) := sorry

/-- The derived naive cotangent complex of a syntomic morphism has Tor-amplitude in `[-1, 0]`. -/
theorem naiveCotangent_hasTorAmplitudeIn_of_syntomic {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Syntomic f] :
    RingedSpace.HasTorAmplitudeIn
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0 := sorry

/-- The naive cotangent complex of a syntomic morphism, bundled in the domain of the
determinant functor. -/
noncomputable def naiveCotangentObject {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f] :
    PerfectDerived.TorNegOneZero Y :=
  ⟨⟨(DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom) :
        Y.toRingedSpace.ModuleDerived),
      naiveCotangent_isPerfect_of_syntomic f⟩,
    naiveCotangent_hasTorAmplitudeIn_of_syntomic f⟩

/-- Forgetting the perfectness and Tor-amplitude witnesses recovers the derived naive
cotangent complex. -/
theorem naiveCotangentObject_obj {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f] :
    (naiveCotangentObject f).obj.obj =
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom) :
        Y.toRingedSpace.ModuleDerived) := sorry

/-- In an open pullback square with syntomic right edge, the left-edge naive cotangent complex
is perfect. -/
theorem baseChangedNaiveCotangent_isPerfect
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    RingedSpace.ModuleDerived.IsPerfect
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f'.toShHom)) := sorry

/-- In an open pullback square with syntomic right edge, the left-edge naive cotangent complex
has Tor-amplitude in `[-1, 0]`. -/
theorem baseChangedNaiveCotangent_hasTorAmplitudeIn
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    RingedSpace.HasTorAmplitudeIn
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f'.toShHom)) (-1) 0 := sorry

/-- The naive cotangent complex on the left edge of an open pullback square, bundled in the
domain of the determinant functor. -/
noncomputable def baseChangedNaiveCotangentObject
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    PerfectDerived.TorNegOneZero Y' :=
  ⟨⟨(DerivedCategory.Q.obj (RingedSpace.naiveCotangent f'.toShHom) :
        Y'.toRingedSpace.ModuleDerived),
      baseChangedNaiveCotangent_isPerfect b f' f a sq⟩,
    baseChangedNaiveCotangent_hasTorAmplitudeIn b f' f a sq⟩

/-- Forgetting the bundled witnesses from the base-changed object recovers the naive cotangent
complex of the left edge. -/
theorem baseChangedNaiveCotangentObject_obj
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    (baseChangedNaiveCotangentObject b f' f a sq).obj.obj =
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f'.toShHom) :
        Y'.toRingedSpace.ModuleDerived) := sorry

/-- The naive cotangent object of a locally quasi-finite syntomic morphism has determinant
rank zero. -/
theorem naiveCotangent_isRankZero
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) :
    D.isRankZero (naiveCotangentObject f) := sorry

/-- The base-changed naive cotangent object in an open pullback square has determinant rank
zero. -/
theorem baseChangedNaiveCotangent_isRankZero
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y') :
    D.isRankZero (baseChangedNaiveCotangentObject b f' f a sq) := sorry

/-- The discriminant section of the determinant line of the naive cotangent complex, viewed as
a morphism from the structure module. -/
noncomputable def discriminantSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) :
    SheafOfModules.RingedSite.unitModule
        (Opens.grothendieckTopology Y) Y.sheaf ⟶
      D.line (naiveCotangentObject f) :=
  RingedSpace.topSectionMorphism (D.line (naiveCotangentObject f))
    (D.canonicalElement (naiveCotangentObject f) (naiveCotangent_isRankZero f D))

/-- The discriminant-section morphism is classified by the canonical determinant element. -/
theorem discriminantSection_def
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) :
    discriminantSection f D =
      RingedSpace.topSectionMorphism (D.line (naiveCotangentObject f))
        (D.canonicalElement (naiveCotangentObject f) (naiveCotangent_isRankZero f D)) := sorry

/-- The discriminant section for the left edge of an open pullback square. -/
noncomputable def baseChangedDiscriminantSection
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y') :
    SheafOfModules.RingedSite.unitModule
        (Opens.grothendieckTopology Y') Y'.sheaf ⟶
      D.line (baseChangedNaiveCotangentObject b f' f a sq) :=
  RingedSpace.topSectionMorphism
    (D.line (baseChangedNaiveCotangentObject b f' f a sq))
    (D.canonicalElement (baseChangedNaiveCotangentObject b f' f a sq)
      (baseChangedNaiveCotangent_isRankZero b f' f a sq D))

/-- The base-changed discriminant-section morphism is classified by the canonical determinant
element. -/
theorem baseChangedDiscriminantSection_def
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y') :
    baseChangedDiscriminantSection b f' f a sq D =
      RingedSpace.topSectionMorphism
        (D.line (baseChangedNaiveCotangentObject b f' f a sq))
        (D.canonicalElement (baseChangedNaiveCotangentObject b f' f a sq)
          (baseChangedNaiveCotangent_isRankZero b f' f a sq D)) := sorry

/-- Condition (1) for a comparison family: degree zero carries the exterior unit to the
canonical discriminant section. -/
def MapsUnitToDiscriminant
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y)
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          D.line (naiveCotangentObject f)) : Prop :=
  SheafOfModules.RingedSite.ExteriorPower.one Y.sheaf
      Ω[(terminal.from Y).toShHom] ≫ c 0 =
    (RingedSpace.unitIsoTensorUnit Y.toRingedSpace).hom ≫
      (λ_ (𝟙_ Y.Modules)).inv ≫
      SheafOfModules.RingedSite.moduleTensorMap (𝒪 := Y.sheaf)
        (((Scheme.Modules.pullbackUnitIso f).inv ≫
          (Scheme.Modules.pullback f).map
            (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
          (Scheme.Modules.pullback f).map
            (SheafOfModules.RingedSite.ExteriorPower.one X.sheaf
              Ω[(terminal.from X).toShHom])) :
            (𝟙_ Y.Modules) ⟶
              (Scheme.Modules.pullback f).obj (Λ[0] Ω[(terminal.from X).toShHom]))
        (((RingedSpace.unitIsoTensorUnit Y.toRingedSpace).inv ≫
          discriminantSection f D) :
            (𝟙_ Y.Modules) ⟶ D.line (naiveCotangentObject f))

/-- The degree-zero condition is precisely the equation sending the unit to the discriminant
section. -/
theorem mapsUnitToDiscriminant_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y)
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          D.line (naiveCotangentObject f)) :
    MapsUnitToDiscriminant f D c ↔
      SheafOfModules.RingedSite.ExteriorPower.one Y.sheaf
          Ω[(terminal.from Y).toShHom] ≫ c 0 =
        (RingedSpace.unitIsoTensorUnit Y.toRingedSpace).hom ≫
          (λ_ (𝟙_ Y.Modules)).inv ≫
          SheafOfModules.RingedSite.moduleTensorMap (𝒪 := Y.sheaf)
            (((Scheme.Modules.pullbackUnitIso f).inv ≫
              (Scheme.Modules.pullback f).map
                (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
              (Scheme.Modules.pullback f).map
                (SheafOfModules.RingedSite.ExteriorPower.one X.sheaf
                  Ω[(terminal.from X).toShHom])) :
                (𝟙_ Y.Modules) ⟶
                  (Scheme.Modules.pullback f).obj (Λ[0] Ω[(terminal.from X).toShHom]))
            (((RingedSpace.unitIsoTensorUnit Y.toRingedSpace).inv ≫
              discriminantSection f D) :
                (𝟙_ Y.Modules) ⟶ D.line (naiveCotangentObject f)) := sorry

/-- The pullback of absolute wedge multiplication along a scheme morphism. -/
noncomputable def pullbackAbsoluteWedge
    {X Y : Scheme.{u}} (f : Y ⟶ X) (q p : ℕ) :
    (Scheme.Modules.pullback f).obj (Λ[q] Ω[(terminal.from X).toShHom]) ⊗
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⟶
      (Scheme.Modules.pullback f).obj (Λ[q + p] Ω[(terminal.from X).toShHom]) :=
  Scheme.Modules.pullbackTensorMap f
    (SheafOfModules.RingedSite.ExteriorPower.mul X.sheaf
      Ω[(terminal.from X).toShHom] q p)

/-- Pullback absolute wedge multiplication is the monoidal pullback of the absolute wedge. -/
theorem pullbackAbsoluteWedge_def
    {X Y : Scheme.{u}} (f : Y ⟶ X) (q p : ℕ) :
    pullbackAbsoluteWedge f q p =
      Scheme.Modules.pullbackTensorMap f
        (SheafOfModules.RingedSite.ExteriorPower.mul X.sheaf
          Ω[(terminal.from X).toShHom] q p) := sorry

/-- Condition (2) for a comparison family: it commutes with left wedge multiplication by
pulled-back absolute forms from the base. -/
def CompatibleWithWedge
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y)
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          D.line (naiveCotangentObject f)) : Prop :=
  ∀ q p : ℕ,
    tensorHom (absoluteFormComparison f q)
        (𝟙 (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
        SheafOfModules.RingedSite.ExteriorPower.mul Y.sheaf
          Ω[(terminal.from Y).toShHom] q p ≫
          c (q + p) =
      ((Scheme.Modules.pullback f).obj
          (Λ[q] Ω[(terminal.from X).toShHom]) ◁ c p) ≫
        (α_ ((Scheme.Modules.pullback f).obj
            (Λ[q] Ω[(terminal.from X).toShHom]))
          ((Scheme.Modules.pullback f).obj
            (Λ[p] Ω[(terminal.from X).toShHom]))
          (D.line (naiveCotangentObject f))).inv ≫
        (pullbackAbsoluteWedge f q p ▷ D.line (naiveCotangentObject f))

/-- Wedge compatibility is precisely the family of homogeneous multiplication squares. -/
theorem compatibleWithWedge_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y)
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y).toShHom]) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          D.line (naiveCotangentObject f)) :
    CompatibleWithWedge f D c ↔
      ∀ q p : ℕ,
        tensorHom (absoluteFormComparison f q)
            (𝟙 (Λ[p] Ω[(terminal.from Y).toShHom])) ≫
            SheafOfModules.RingedSite.ExteriorPower.mul Y.sheaf
              Ω[(terminal.from Y).toShHom] q p ≫
              c (q + p) =
          ((Scheme.Modules.pullback f).obj
              (Λ[q] Ω[(terminal.from X).toShHom]) ◁ c p) ≫
            (α_ ((Scheme.Modules.pullback f).obj
                (Λ[q] Ω[(terminal.from X).toShHom]))
              ((Scheme.Modules.pullback f).obj
                (Λ[p] Ω[(terminal.from X).toShHom]))
              (D.line (naiveCotangentObject f))).inv ≫
            (pullbackAbsoluteWedge f q p ▷ D.line (naiveCotangentObject f)) := sorry

/-- Condition (1) for a comparison family on the left edge of an open pullback square. -/
def BaseChangedMapsUnitToDiscriminant
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y')
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y').toShHom]) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          D.line (baseChangedNaiveCotangentObject b f' f a sq)) : Prop :=
  SheafOfModules.RingedSite.ExteriorPower.one Y'.sheaf
      Ω[(terminal.from Y').toShHom] ≫ c 0 =
    (RingedSpace.unitIsoTensorUnit Y'.toRingedSpace).hom ≫
      (λ_ (𝟙_ Y'.Modules)).inv ≫
      SheafOfModules.RingedSite.moduleTensorMap (𝒪 := Y'.sheaf)
        (((Scheme.Modules.pullbackUnitIso f').inv ≫
          (Scheme.Modules.pullback f').map
            (RingedSpace.unitIsoTensorUnit X'.toRingedSpace).inv ≫
          (Scheme.Modules.pullback f').map
            (SheafOfModules.RingedSite.ExteriorPower.one X'.sheaf
              Ω[(terminal.from X').toShHom])) :
            (𝟙_ Y'.Modules) ⟶
              (Scheme.Modules.pullback f').obj (Λ[0] Ω[(terminal.from X').toShHom]))
        (((RingedSpace.unitIsoTensorUnit Y'.toRingedSpace).inv ≫
          baseChangedDiscriminantSection b f' f a sq D) :
            (𝟙_ Y'.Modules) ⟶
              D.line (baseChangedNaiveCotangentObject b f' f a sq))

/-- The base-changed degree-zero condition is precisely the equation sending the unit to the
base-changed discriminant section. -/
theorem baseChangedMapsUnitToDiscriminant_iff
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y')
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y').toShHom]) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          D.line (baseChangedNaiveCotangentObject b f' f a sq)) :
    BaseChangedMapsUnitToDiscriminant b f' f a sq D c ↔
      SheafOfModules.RingedSite.ExteriorPower.one Y'.sheaf
          Ω[(terminal.from Y').toShHom] ≫ c 0 =
        (RingedSpace.unitIsoTensorUnit Y'.toRingedSpace).hom ≫
          (λ_ (𝟙_ Y'.Modules)).inv ≫
          SheafOfModules.RingedSite.moduleTensorMap (𝒪 := Y'.sheaf)
            (((Scheme.Modules.pullbackUnitIso f').inv ≫
              (Scheme.Modules.pullback f').map
                (RingedSpace.unitIsoTensorUnit X'.toRingedSpace).inv ≫
              (Scheme.Modules.pullback f').map
                (SheafOfModules.RingedSite.ExteriorPower.one X'.sheaf
                  Ω[(terminal.from X').toShHom])) :
                (𝟙_ Y'.Modules) ⟶
                  (Scheme.Modules.pullback f').obj (Λ[0] Ω[(terminal.from X').toShHom]))
            (((RingedSpace.unitIsoTensorUnit Y'.toRingedSpace).inv ≫
              baseChangedDiscriminantSection b f' f a sq D) :
                (𝟙_ Y'.Modules) ⟶
                  D.line (baseChangedNaiveCotangentObject b f' f a sq)) := sorry

/-- Condition (2) for a comparison family on the left edge of an open pullback square. -/
def BaseChangedCompatibleWithWedge
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y')
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y').toShHom]) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          D.line (baseChangedNaiveCotangentObject b f' f a sq)) : Prop :=
  ∀ q p : ℕ,
    tensorHom (absoluteFormComparison f' q)
        (𝟙 (Λ[p] Ω[(terminal.from Y').toShHom])) ≫
        SheafOfModules.RingedSite.ExteriorPower.mul Y'.sheaf
          Ω[(terminal.from Y').toShHom] q p ≫
          c (q + p) =
      ((Scheme.Modules.pullback f').obj
          (Λ[q] Ω[(terminal.from X').toShHom]) ◁ c p) ≫
        (α_ ((Scheme.Modules.pullback f').obj
            (Λ[q] Ω[(terminal.from X').toShHom]))
          ((Scheme.Modules.pullback f').obj
            (Λ[p] Ω[(terminal.from X').toShHom]))
          (D.line (baseChangedNaiveCotangentObject b f' f a sq))).inv ≫
        (pullbackAbsoluteWedge f' q p ▷
          D.line (baseChangedNaiveCotangentObject b f' f a sq))

/-- Base-changed wedge compatibility is precisely the family of homogeneous multiplication
squares. -/
theorem baseChangedCompatibleWithWedge_iff
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y')
    (c : ∀ p : ℕ,
      (Λ[p] Ω[(terminal.from Y').toShHom]) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          D.line (baseChangedNaiveCotangentObject b f' f a sq)) :
    BaseChangedCompatibleWithWedge b f' f a sq D c ↔
      ∀ q p : ℕ,
        tensorHom (absoluteFormComparison f' q)
            (𝟙 (Λ[p] Ω[(terminal.from Y').toShHom])) ≫
            SheafOfModules.RingedSite.ExteriorPower.mul Y'.sheaf
              Ω[(terminal.from Y').toShHom] q p ≫
              c (q + p) =
          ((Scheme.Modules.pullback f').obj
              (Λ[q] Ω[(terminal.from X').toShHom]) ◁ c p) ≫
            (α_ ((Scheme.Modules.pullback f').obj
                (Λ[q] Ω[(terminal.from X').toShHom]))
              ((Scheme.Modules.pullback f').obj
                (Λ[p] Ω[(terminal.from X').toShHom]))
              (D.line (baseChangedNaiveCotangentObject b f' f a sq))).inv ≫
            (pullbackAbsoluteWedge f' q p ▷
              D.line (baseChangedNaiveCotangentObject b f' f a sq)) := sorry

/-- The canonical comparison between the two iterated pullbacks around a commutative square. -/
noncomputable def iteratedPullbackIso
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) (M : X.Modules) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback a).obj M) :=
  (Scheme.Modules.pullbackComp b f).app M ≪≫
    (Scheme.Modules.pullbackCongr sq.w).app M ≪≫
      ((Scheme.Modules.pullbackComp f' a).app M).symm

/-- The iterated-pullback comparison is the composite induced by the commutative square. -/
theorem iteratedPullbackIso_def
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) (M : X.Modules) :
    iteratedPullbackIso b f' f a sq M =
      (Scheme.Modules.pullbackComp b f).app M ≪≫
        (Scheme.Modules.pullbackCongr sq.w).app M ≪≫
          ((Scheme.Modules.pullbackComp f' a).app M).symm := sorry

/-- The comparison of absolute forms on the base after traversing a commutative square. -/
noncomputable def targetAbsoluteFormComparison
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) (p : ℕ) :
    (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom])) ⟶
      (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) :=
  (iteratedPullbackIso b f' f a sq (Λ[p] Ω[(terminal.from X).toShHom])).hom ≫
    (Scheme.Modules.pullback f').map (absoluteFormComparison a p)

/-- The target absolute-form comparison uses pullback composition and the absolute-form map
along the bottom edge. -/
theorem targetAbsoluteFormComparison_def
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) (p : ℕ) :
    targetAbsoluteFormComparison b f' f a sq p =
      (iteratedPullbackIso b f' f a sq
          (Λ[p] Ω[(terminal.from X).toShHom])).hom ≫
        (Scheme.Modules.pullback f').map (absoluteFormComparison a p) := sorry

/-- The canonical derived naive-cotangent comparison is invertible for an open pullback square
with syntomic right edge. -/
instance naiveCotangentDerivedComparison_isIso
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    IsIso (derivedComparison sq) := sorry

/-- The canonical naive-cotangent base-change isomorphism in the determinant domain. -/
noncomputable def naiveCotangentDerivedComparisonIso
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    (PerfectDerived.TorNegOneZero.pullback b).obj (naiveCotangentObject f) ≅
      baseChangedNaiveCotangentObject b f' f a sq :=
  ObjectProperty.isoMk
    (fun K : RingedSpace.ModuleDerived.Perfect (X := Y'.toRingedSpace) ↦
      RingedSpace.HasTorAmplitudeIn K.obj (-1) 0)
    (ObjectProperty.isoMk RingedSpace.ModuleDerived.perfect
      (@asIso _ _ _ _ (derivedComparison sq)
        (naiveCotangentDerivedComparison_isIso (b := b) (f' := f')
          (f := f) (a := a) (sq := sq))))

/-- The forward map of the canonical lifted isomorphism is the derived naive-cotangent
comparison. -/
theorem naiveCotangentDerivedComparisonIso_hom
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    (naiveCotangentDerivedComparisonIso b f' f a sq).hom =
      ObjectProperty.homMk (ObjectProperty.homMk (derivedComparison sq)) := sorry

/-- A derived isomorphism induces the corresponding isomorphism of determinant lines. -/
noncomputable def determinantLineIso
    {Y : Scheme.{u}} (D : PerfectDerived.TorNegOneZero.Determinant Y)
    {K L : PerfectDerived.TorNegOneZero Y} (e : K ≅ L) :
    D.line K ≅ D.line L :=
  (ObjectProperty.ι (fun L : Y.Modules ↦ Scheme.Modules.Invertible L)).mapIso
    (D.det.map ⟨e⟩).iso

/-- The determinant-line isomorphism is induced by the determinant functor on the supplied
derived isomorphism. -/
theorem determinantLineIso_hom
    {Y : Scheme.{u}} (D : PerfectDerived.TorNegOneZero.Determinant Y)
    {K L : PerfectDerived.TorNegOneZero Y} (e : K ≅ L) :
    (determinantLineIso D e).hom = (D.det.map ⟨e⟩).iso.hom.hom := sorry

/-- The determinant-line base-change isomorphism attached to the open pullback square. -/
noncomputable def determinantLineBaseChangeIso
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f]
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) :
    (Scheme.Modules.pullback b).obj (P.source.line (naiveCotangentObject f)) ≅
      P.target.line (baseChangedNaiveCotangentObject b f' f a sq) :=
  P.lineIso (naiveCotangentObject f) ≪≫
    determinantLineIso P.target (naiveCotangentDerivedComparisonIso b f' f a sq)

/-- The determinant-line base-change isomorphism is the determinant pullback comparison
followed by the determinant of the canonical naive-cotangent base-change isomorphism. -/
theorem determinantLineBaseChangeIso_hom
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f]
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) :
    (determinantLineBaseChangeIso b f' f a sq P).hom =
      (P.lineIso (naiveCotangentObject f)).hom ≫
        (determinantLineIso P.target
          (naiveCotangentDerivedComparisonIso b f' f a sq)).hom := sorry

/-- The canonical determinant-line comparison carries the pulled-back discriminant section to
the base-changed discriminant section. -/
theorem determinantLineBaseChangeIso_discriminantSection
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) :
    (Scheme.Modules.pullbackUnitIso b).inv ≫
        (Scheme.Modules.pullback b).map
          ((RingedSpace.unitIsoTensorUnit Y.toRingedSpace).inv ≫
            discriminantSection f P.source) ≫
          (determinantLineBaseChangeIso b f' f a sq P).hom =
      (RingedSpace.unitIsoTensorUnit Y'.toRingedSpace).inv ≫
        baseChangedDiscriminantSection b f' f a sq P.target := sorry

/-- The target-side comparison in the base-change square, assembled from pullback monoidality,
the absolute-form comparison along `a`, and determinant-line base change. -/
noncomputable def comparisonTargetMap
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f]
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) (p : ℕ) :
    (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          P.source.line (naiveCotangentObject f)) ⟶
      (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
        P.target.line (baseChangedNaiveCotangentObject b f' f a sq) :=
  Scheme.Modules.pullbackTensorComparison b _ _ ≫
    tensorHom (targetAbsoluteFormComparison b f' f a sq p)
      (determinantLineBaseChangeIso b f' f a sq P).hom

/-- The target comparison is the tensor of the canonical form and determinant-line
comparisons after the monoidal pullback map. -/
theorem comparisonTargetMap_def
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f]
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) (p : ℕ) :
    comparisonTargetMap b f' f a sq P p =
      Scheme.Modules.pullbackTensorComparison b _ _ ≫
        tensorHom (targetAbsoluteFormComparison b f' f a sq p)
          (determinantLineBaseChangeIso b f' f a sq P).hom := sorry

/-- The exterior-form generators obtained from forms pulled back from `X'` and from `Y`. -/
noncomputable def exteriorFormGenerator
    {X' Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (p : ℕ) :
    (∐ fun i : Fin (p + 1) ↦
      (Scheme.Modules.pullback f').obj
          (Λ[i.1] Ω[(terminal.from X').toShHom]) ⊗
        (Scheme.Modules.pullback b).obj
          (Λ[p - i.1] Ω[(terminal.from Y).toShHom])) ⟶
      Λ[p] Ω[(terminal.from Y').toShHom] :=
  Sigma.desc fun i ↦
    tensorHom (absoluteFormComparison f' i.1)
        (absoluteFormComparison b (p - i.1)) ≫
      SheafOfModules.RingedSite.ExteriorPower.mul Y'.sheaf
        Ω[(terminal.from Y').toShHom] i.1 (p - i.1) ≫
      eqToHom (congrArg (fun n ↦ Λ[n] Ω[(terminal.from Y').toShHom])
        (Nat.add_sub_of_le (Nat.le_of_lt_succ i.2)))

/-- The displayed exterior-form generator map is epic when the square identifies `Y'` with an
open subscheme of the fibre product. -/
theorem exteriorFormGenerator_epi_of_openPullback
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)] {p : ℕ} :
    Epi (exteriorFormGenerator b f' p) := sorry


/-- Under an open pullback, comparison families satisfying the unit, wedge, and base-change conditions are unique. -/
theorem comparisonFamily_unique
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a)
    [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    (P : Pullback b)
    (c : ∀ p : ℕ,
      (Λ[p] (Ω[(terminal.from Y).toShHom])) ⟶
        (Scheme.Modules.pullback f).obj (Λ[p] Ω[(terminal.from X).toShHom]) ⊗
          P.source.line (naiveCotangentObject f))
    (hcOne : MapsUnitToDiscriminant f P.source c)
    (hcWedge : CompatibleWithWedge f P.source c)
    (c₁ c₂ : ∀ p : ℕ,
      (Λ[p] (Ω[(terminal.from Y').toShHom])) ⟶
        (Scheme.Modules.pullback f').obj (Λ[p] Ω[(terminal.from X').toShHom]) ⊗
          P.target.line (baseChangedNaiveCotangentObject b f' f a sq))
    (hc₁one : BaseChangedMapsUnitToDiscriminant b f' f a sq P.target c₁)
    (hc₁wedge : BaseChangedCompatibleWithWedge b f' f a sq P.target c₁)
    (hc₂one : BaseChangedMapsUnitToDiscriminant b f' f a sq P.target c₂)
    (hc₂wedge : BaseChangedCompatibleWithWedge b f' f a sq P.target c₂)
    (hc₁baseChange : ∀ p : ℕ,
      (Scheme.Modules.pullback b).map (c p) ≫
          comparisonTargetMap b f' f a sq P p =
        absoluteFormComparison b p ≫ c₁ p)
    (hc₂baseChange : ∀ p : ℕ,
      (Scheme.Modules.pullback b).map (c p) ≫
          comparisonTargetMap b f' f a sq P p =
        absoluteFormComparison b p ≫ c₂ p) :
    c₁ = c₂ := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
