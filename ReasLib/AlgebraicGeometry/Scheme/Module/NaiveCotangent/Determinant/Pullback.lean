module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Determinant
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.BaseChange.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DeterminantComparison
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Tate

open NaiveCotangent.BaseChange

/-- The derived naive-cotangent comparison is invertible for an open pullback square with
syntomic right edge. -/
instance derivedComparisonIsIso
    {X' X Y' Y : Scheme.{u}}
    {b : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {a : X' ⟶ X}
    {sq : CommSq b f' f a} [IsOpenImmersion (pullback.lift b f' sq.w)] [Syntomic f] :
    IsIso (derivedComparison sq) := sorry

/-- The canonical naive-cotangent isomorphism induced by an open pullback square. -/
noncomputable def cotangentIso
    {X' X Y' Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y'.toRingedSpace)]
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f'] :
    (PerfectDerived.TorNegOneZero.pullback b).obj (cotangentObject f) ≅
      cotangentObject f' :=
  ObjectProperty.isoMk
    (fun K : RingedSpace.ModuleDerived.Perfect (X := Y'.toRingedSpace) ↦
      RingedSpace.HasTorAmplitudeIn K.obj (-1) 0)
    (ObjectProperty.isoMk RingedSpace.ModuleDerived.perfect
      (@asIso _ _ _ _ (derivedComparison sq)
        (derivedComparisonIsIso (b := b) (f' := f')
          (f := f) (a := a) (sq := sq))))

/-- The forward map of `cotangentIso` is the canonical derived naive-cotangent comparison. -/
theorem cotangentIso_hom
    {X' X Y' Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y'.toRingedSpace)]
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f'] :
    (cotangentIso b f' f a sq).hom =
      ObjectProperty.homMk (ObjectProperty.homMk (derivedComparison sq)) := sorry

/-- The determinant-line comparison associated to an open pullback square. -/
noncomputable def baseChangeIso
    {X' X Y' Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y'.toRingedSpace)]
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f']
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) :
    (Scheme.Modules.pullback b).obj (P.source.line (cotangentObject f)) ≅
      P.target.line (cotangentObject f') :=
  P.lineIso (cotangentObject f) ≪≫
    Scheme.RelativeDifferentials.determinantLineIso P.target (cotangentIso b f' f a sq)

/-- The base-change isomorphism is the pullback comparison followed by the determinant of the
cotangent comparison. -/
theorem baseChangeIso_hom
    {X' X Y' Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y'.toRingedSpace)]
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [Syntomic f] [Syntomic f']
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) :
    (baseChangeIso b f' f a sq P).hom =
      (P.lineIso (cotangentObject f)).hom ≫
        (Scheme.RelativeDifferentials.determinantLineIso
          P.target (cotangentIso b f' f a sq)).hom := sorry

/-- The determinant-line base-change comparison carries the pulled-back determinant section
to the determinant section of the base-changed morphism. -/
theorem baseChangeIso_delta
    {X' X Y' Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y'.toRingedSpace)]
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : CommSq b f' f a) [IsOpenImmersion (pullback.lift b f' sq.w)]
    [LocallyQuasiFinite f] [Syntomic f]
    [LocallyQuasiFinite f'] [Syntomic f']
    (P : PerfectDerived.TorNegOneZero.Determinant.Pullback b) :
    SheafOfModules.sectionsMap (baseChangeIso b f' f a sq P).hom
        (RingedSpace.Hom.pullbackSections b.toShHom (delta f P.source)) =
      delta f' P.target := sorry

end AlgebraicGeometry.Scheme.Hom.Tate
