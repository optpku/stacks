/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal

/-!
# Associated sheaves of pullback effective Cartier divisors

The pullback of the sheaf associated to an effective Cartier divisor is canonically the
associated sheaf of its inverse-image divisor, compatibly with canonical sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S S' : Scheme.{u}}

/-- The pullback of an ideal sheaf maps canonically to the ideal sheaf of the inverse-image
divisor. -/
noncomputable def idealSheafPullbackComparison
    (D : S.IdealSheafData) (f : S' ⟶ S) :
    (Scheme.Modules.pullback f).obj (Subobject.underlying.obj D.toSubobject) ⟶
      Subobject.underlying.obj (D.comap f).toSubobject :=
  LocallyRingedSpace.IdealSubobject.pullbackFactor D.toSubobject f.toLRSHom ≫
    eqToHom (congrArg Subobject.underlying.obj (D.toSubobject_comap f).symm)

/-- For an effective Cartier divisor with defined pullback, the canonical comparison of ideal
sheaves is invertible. -/
noncomputable instance idealSheafPullbackComparison_isIso
    (D : S.IdealSheafData) (f : S' ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι] :
    IsIso (D.idealSheafPullbackComparison f) := sorry

/-- Pullback of the internal-Hom dual of an effective Cartier ideal maps canonically to the
internal Hom from the pulled-back ideal to the target structure sheaf. -/
noncomputable def associatedSheafPullbackComparison
    (D : S.IdealSheafData) (f : S' ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    (Scheme.Modules.pullback f).obj D.associatedSheaf ⟶
      (ihom ((Scheme.Modules.pullback f).obj
        (Subobject.underlying.obj D.toSubobject))).obj
          (SheafOfModules.unit S'.ringCatSheaf) :=
  @Functor.LaxMonoidal.InternalHom.comparison _ _ _ _ _ _
      (Scheme.Modules.pullback f)
        (AlgebraicGeometry.Scheme.Modules.pullbackMonoidal f).toLaxMonoidal
        (Subobject.underlying.obj D.toSubobject)
        (SheafOfModules.unit S.ringCatSheaf) _ _ ≫
    (ihom ((Scheme.Modules.pullback f).obj
      (Subobject.underlying.obj D.toSubobject))).map
        (SheafOfModules.pullbackObjUnitToUnit
          (RingedSpace.Hom.toRingCatSheafHom f.toShHom))

/-- The canonical pullback comparison for the associated sheaf of an effective Cartier divisor
is invertible. -/
noncomputable instance associatedSheafPullbackComparison_isIso
    (D : S.IdealSheafData) (f : S' ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    IsIso (D.associatedSheafPullbackComparison f) := sorry

/-- Pullback of the sheaf associated to an effective Cartier divisor is canonically isomorphic
to the sheaf associated to its inverse-image divisor. -/
noncomputable def associatedSheafPullbackIso
    (D : S.IdealSheafData) (f : S' ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι] :
    (Scheme.Modules.pullback f).obj D.associatedSheaf ≅
      (D.comap f).associatedSheaf :=
  asIso (D.associatedSheafPullbackComparison f) ≪≫
    (@asIso _ _ _ _
      ((MonoidalClosed.pre (D.idealSheafPullbackComparison f)).app
        (SheafOfModules.unit S'.ringCatSheaf)) (by
          change IsIso ((MonoidalClosed.internalHom.map
            (D.idealSheafPullbackComparison f).op).app _)
          infer_instance)).symm

/-- The canonical pullback isomorphism for associated sheaves carries the pulled-back canonical
section to the canonical section of the inverse-image divisor. -/
theorem associatedSheafPullbackIso_canonicalSection
    (D : S.IdealSheafData) (f : S' ⟶ S)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι] :
    SheafOfModules.sectionsMap (D.associatedSheafPullbackIso f).hom
        (RingedSpace.Hom.pullbackSections f.toShHom D.canonicalSection) =
      (D.comap f).canonicalSection := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
