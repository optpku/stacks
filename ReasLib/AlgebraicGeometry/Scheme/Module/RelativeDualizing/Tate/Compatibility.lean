/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Determinant
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Determinant.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.Tate

open PerfectDerived.TorNegOneZero

/-- A presentation of the pullback of a relative dualizing sheaf as a relative dualizing
sheaf on an open pullback square. -/
structure DualizingPullback.{v}
    {X' X Y' Y : Scheme.{v}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    (W : f.RelativeDualizingSheaf) where
  /-- The relative dualizing sheaf structure on the pulled-back module. -/
  model : f'.RelativeDualizingSheaf
  /-- Its underlying module is the pullback of the source relative dualizing module. -/
  module_eq : model.module.obj = (Scheme.Modules.pullback b).obj W.module.obj
  /-- Pullback of a trace section is a trace section in the presented affine model. -/
  pullback_trace : ∀ (τ : (W.module.obj).sections), W.IsTraceSection τ →
    model.IsTraceSection
      (SheafOfModules.sectionsMap (eqToIso module_eq.symm).hom
        (RingedSpace.Hom.pullbackSections b.toShHom τ))

namespace DualizingPullback

/-- Construct a presented relative-dualizing pullback from its full affine model and the
identification of its underlying module. -/
def of
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    (W : f.RelativeDualizingSheaf) (model : f'.RelativeDualizingSheaf)
    (module_eq : model.module.obj = (Scheme.Modules.pullback b).obj W.module.obj)
    (pullback_trace : ∀ (τ : (W.module.obj).sections), W.IsTraceSection τ →
      model.IsTraceSection
        (SheafOfModules.sectionsMap (eqToIso module_eq.symm).hom
          (RingedSpace.Hom.pullbackSections b.toShHom τ))) :
    DualizingPullback b f' f a sq W :=
  ⟨model, module_eq, pullback_trace⟩

/-- The canonical module isomorphism underlying a presented relative-dualizing pullback. -/
def moduleIso
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    {W : f.RelativeDualizingSheaf} (B : DualizingPullback b f' f a sq W) :
    (Scheme.Modules.pullback b).obj W.module.obj ≅ (B.model.module).obj :=
  eqToIso B.module_eq.symm

/-- The module comparison of a presented pullback is induced by its underlying equality. -/
theorem moduleIso_eq
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    {W : f.RelativeDualizingSheaf} (B : DualizingPullback b f' f a sq W) :
    B.moduleIso = eqToIso B.module_eq.symm := sorry

/-- Relative dualizing sheaves admit a presentation on every open pullback square whose
underlying module and trace section are the corresponding pullbacks. -/
theorem nonempty
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    (W : f.RelativeDualizingSheaf) :
    Nonempty (DualizingPullback b f' f a sq W) := sorry

end DualizingPullback

/-- A relative-dualizing base-change isomorphism is canonical when, after the presented
pullback identification, it preserves every affine identification and restriction transition. -/
def IsDualizingBaseChangeIso
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    {W : f.RelativeDualizingSheaf} (B : DualizingPullback b f' f a sq W)
    (W' : f'.RelativeDualizingSheaf)
    (eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj) : Prop :=
  RelativeDualizingSheaf.Compatible f' B.model W' (B.moduleIso.symm ≪≫ eω)

/-- Canonical relative-dualizing base-change isomorphisms are exactly those compatible with
all affine presentation identifications and restriction transitions. -/
theorem isDualizingBaseChangeIso_iff
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    {W : f.RelativeDualizingSheaf} (B : DualizingPullback b f' f a sq W)
    (W' : f'.RelativeDualizingSheaf)
    (eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj) :
    IsDualizingBaseChangeIso B W' eω ↔
      RelativeDualizingSheaf.Compatible f' B.model W' (B.moduleIso.symm ≪≫ eω) := sorry

/-- A presented relative-dualizing pullback has a unique comparison with any other relative
dualizing sheaf that is compatible with all affine presentation data. -/
theorem existsUniqueDualizingBaseChangeIso
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    {W : f.RelativeDualizingSheaf} (B : DualizingPullback b f' f a sq W)
    (W' : f'.RelativeDualizingSheaf) :
    ∃! eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj,
      IsDualizingBaseChangeIso B W' eω := sorry

/-- A canonical presentation-compatible dualizing comparison carries the pulled-back trace
section to the target trace section. -/
theorem IsDualizingBaseChangeIso.maps_trace
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    {W : f.RelativeDualizingSheaf} (B : DualizingPullback b f' f a sq W)
    (W' : f'.RelativeDualizingSheaf)
    (τ : (W.module.obj).sections) (τ' : (W'.module.obj).sections)
    (hτ : W.IsTraceSection τ) (hτ' : W'.IsTraceSection τ')
    (eω : (Scheme.Modules.pullback b).obj W.module.obj ≅ W'.module.obj)
    (heω : IsDualizingBaseChangeIso B W' eω) :
    SheafOfModules.sectionsMap eω.hom
      (RingedSpace.Hom.pullbackSections b.toShHom τ) = τ' := sorry

end Scheme.Hom.Tate
end AlgebraicGeometry
