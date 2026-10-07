module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Determinant.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.CanonicalPullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Tate.Compatibility

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace ActualTate

/-- The determinant of the naive cotangent complex commutes with pullback along an
open subscheme of a base change of a syntomic morphism. -/
def baseChangeIso {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f'] :
    (Scheme.Modules.pullback b).obj (detNL f) ≅ detNL f' :=
  ActualDeterminantPullback.pullbackIso b (Scheme.Hom.Tate.cotangentObject f) ≪≫
    ActualGlobalDeterminant.lineIso Y' (Scheme.Hom.Tate.cotangentIso b f' f a sq)

/-- The determinant comparison on an open pullback square carries the pulled-back
canonical determinant section to the canonical determinant section. -/
theorem baseChangeIso_delta {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f'] [LocallyQuasiFinite f] [LocallyQuasiFinite f'] :
    SheafOfModules.sectionsMap (baseChangeIso b f' f a sq).hom
      (RingedSpace.Hom.pullbackSections b.toShHom (delta f)) = delta f' := sorry

/-- An assignment of determinant-line isomorphisms to relative dualizing sheaves with
trace sections for locally quasi-finite syntomic morphisms of locally Noetherian schemes. -/
structure Rule where
  component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] [Syntomic f]
    (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections), W.IsTraceSection τ →
      (detNL f ≅ W.module.obj)

/-- Construct a determinant-line rule from an explicit assignment of its component
isomorphisms to relative dualizing sheaves with trace sections. -/
def Rule.of
    (component : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      [LocallyQuasiFinite f] [Syntomic f]
      (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections), W.IsTraceSection τ →
        (detNL f ≅ W.module.obj)) : Rule.{u} :=
  ⟨component⟩

/-- A determinant-line rule preserves the canonical section and commutes with the
relative dualizing comparison on every open pullback square. -/
structure IsRule (r : Rule.{u}) : Prop where
  maps_delta : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] [Syntomic f]
    (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections) (hτ : W.IsTraceSection τ),
      SheafOfModules.sectionsMap (r.component f W τ hτ).hom (delta f) = τ
  naturality : ∀ {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (hτ : W.IsTraceSection τ) (hτ' : W'.IsTraceSection τ')
    (B : Scheme.Hom.Tate.DualizingPullback b f' f a sq W)
    (eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj),
    Scheme.Hom.Tate.IsDualizingBaseChangeIso B W' eω →
      (Scheme.Modules.pullback b).map (r.component f W τ hτ).hom ≫ eω.hom =
        (baseChangeIso b f' f a sq).hom ≫ (r.component f' W' τ' hτ').hom

/-- Construct the law that a determinant-line rule preserves the canonical section
and commutes with the relative dualizing comparison. -/
def IsRule.of {r : Rule.{u}}
    (maps_delta : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      [LocallyQuasiFinite f] [Syntomic f]
      (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections) (hτ : W.IsTraceSection τ),
        SheafOfModules.sectionsMap (r.component f W τ hτ).hom (delta f) = τ)
    (naturality : ∀ {X' X Y' Y : Scheme.{u}}
      (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
      (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
      [LocallyQuasiFinite f] [Syntomic f]
      [LocallyQuasiFinite f'] [Syntomic f']
      (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
      (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
      (hτ : W.IsTraceSection τ) (hτ' : W'.IsTraceSection τ')
      (B : Scheme.Hom.Tate.DualizingPullback b f' f a sq W)
      (eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj),
      Scheme.Hom.Tate.IsDualizingBaseChangeIso B W' eω →
        (Scheme.Modules.pullback b).map (r.component f W τ hτ).hom ≫ eω.hom =
          (baseChangeIso b f' f a sq).hom ≫ (r.component f' W' τ' hτ').hom) :
    IsRule r :=
  ⟨maps_delta, naturality⟩

/-- The determinant-line rule laws are exactly preservation of the canonical section
and compatibility with the relative dualizing comparison. -/
theorem isRule_iff (r : Rule.{u}) :
    IsRule r ↔
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
        [LocallyQuasiFinite f] [Syntomic f]
        (W : f.RelativeDualizingSheaf) (τ : W.module.obj.sections)
        (hτ : W.IsTraceSection τ),
          SheafOfModules.sectionsMap (r.component f W τ hτ).hom (delta f) = τ) ∧
      (∀ {X' X Y' Y : Scheme.{u}}
        (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
        (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
        [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
        [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
        [LocallyQuasiFinite f] [Syntomic f]
        [LocallyQuasiFinite f'] [Syntomic f']
        (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
        (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
        (hτ : W.IsTraceSection τ) (hτ' : W'.IsTraceSection τ')
        (B : Scheme.Hom.Tate.DualizingPullback b f' f a sq W)
        (eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj),
        Scheme.Hom.Tate.IsDualizingBaseChangeIso B W' eω →
          (Scheme.Modules.pullback b).map (r.component f W τ hτ).hom ≫ eω.hom =
            (baseChangeIso b f' f a sq).hom ≫ (r.component f' W' τ' hτ').hom) := sorry

end ActualTate

namespace AlgebraicGeometry.Scheme.Hom.Tate

/-- There is a unique determinant-line rule for locally quasi-finite syntomic morphisms
of locally Noetherian schemes that preserves the canonical section and commutes with
open pullback and base change. -/
theorem existsUnique : ∃! r : ActualTate.Rule.{u}, ActualTate.IsRule r := sorry

end AlgebraicGeometry.Scheme.Hom.Tate
