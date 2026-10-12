/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.Existence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.LocallyQuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

-- This is not an instance because `hX` and `hY` cannot be inferred from `HasPushout i' j'`.
/-- For an admissible lower span, a cartesian diagram whose vertical maps are separated,
locally of finite type, and locally quasi-finite has a pushout on its upper span. -/
theorem hasPushoutOfBaseChange {S : Scheme.{u}} {Z X Y : Over S}
    {Z' X' Y' : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (i' : Z' ⟶ X') (j' : Z' ⟶ Y') (f : X' ⟶ X.left)
    (g : Y' ⟶ Y.left) (h : Z' ⟶ Z.left) [IsAdmissibleSpan i j]
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated g] [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    [IsSeparated h] [LocallyOfFiniteType h] [LocallyQuasiFinite h]
    (hX : IsPullback i' h f i.left) (hY : IsPullback j' h g j.left) :
    HasPushout i' j' := sorry

/-- For an admissible lower span and a cartesian diagram with separated, locally of finite
type, locally quasi-finite vertical maps, the canonical map from the upper pushout to the
lower pushout is separated. -/
instance instPushoutMapIsSeparated {S : Scheme.{u}} {Z X Y : Over S}
    {Z' X' Y' : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (i' : Z' ⟶ X') (j' : Z' ⟶ Y') (f : X' ⟶ X.left)
    (g : Y' ⟶ Y.left) (h : Z' ⟶ Z.left) [IsAdmissibleSpan i j]
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated g] [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    [IsSeparated h] [LocallyOfFiniteType h] [LocallyQuasiFinite h]
    (hX : IsPullback i' h f i.left) (hY : IsPullback j' h g j.left)
    [HasPushout i' j'] :
    IsSeparated
      (pushout.map i' j' i.left j.left f g h hX.w hY.w) := sorry

/-- For an admissible lower span and a cartesian diagram with separated, locally of finite
type, locally quasi-finite vertical maps, the canonical map from the upper pushout to the
lower pushout is locally of finite type. -/
instance instPushoutMapLocallyOfFiniteType {S : Scheme.{u}} {Z X Y : Over S}
    {Z' X' Y' : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (i' : Z' ⟶ X') (j' : Z' ⟶ Y') (f : X' ⟶ X.left)
    (g : Y' ⟶ Y.left) (h : Z' ⟶ Z.left) [IsAdmissibleSpan i j]
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated g] [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    [IsSeparated h] [LocallyOfFiniteType h] [LocallyQuasiFinite h]
    (hX : IsPullback i' h f i.left) (hY : IsPullback j' h g j.left)
    [HasPushout i' j'] :
    LocallyOfFiniteType
      (pushout.map i' j' i.left j.left f g h hX.w hY.w) := sorry

variable {S : Scheme.{u}} {Z X Y : Over S} {Z' X' Y' : Scheme.{u}}
  (i : Z ⟶ X) (j : Z ⟶ Y) (i' : Z' ⟶ X') (j' : Z' ⟶ Y')
  (f : X' ⟶ X.left) (g : Y' ⟶ Y.left) (h : Z' ⟶ Z.left)
  [spanAdmissible : IsAdmissibleSpan i j]
  [fSeparated : IsSeparated f] [fFiniteType : LocallyOfFiniteType f]
  [fQuasiFinite : LocallyQuasiFinite f]
  [gSeparated : IsSeparated g] [gFiniteType : LocallyOfFiniteType g]
  [gQuasiFinite : LocallyQuasiFinite g]
  [hSeparated : IsSeparated h] [hFiniteType : LocallyOfFiniteType h]
  [hQuasiFinite : LocallyQuasiFinite h]
  (hX : IsPullback i' h f i.left) (hY : IsPullback j' h g j.left)

include spanAdmissible fSeparated fFiniteType fQuasiFinite
  gSeparated gFiniteType gQuasiFinite hSeparated hFiniteType hQuasiFinite hX hY

/-- For an admissible lower span and a cartesian diagram with separated, locally of finite
type, locally quasi-finite vertical maps, the square formed by the second coprojections
and the canonical pushout map is a pullback. -/
theorem baseChangeInr_isPullback [HasPushout i' j'] :
    IsPullback (pushout.inr i' j') g
      (pushout.map i' j' i.left j.left f g h hX.w hY.w)
      (pushout.inr i.left j.left) := sorry

/-- For an admissible lower span and a cartesian diagram with separated, locally of finite
type, locally quasi-finite vertical maps, the square formed by the first coprojections
and the canonical pushout map is a pullback. -/
theorem baseChangeInl_isPullback [HasPushout i' j'] :
    IsPullback (pushout.inl i' j') f
      (pushout.map i' j' i.left j.left f g h hX.w hY.w)
      (pushout.inl i.left j.left) := sorry

/-- For an admissible lower span and a cartesian diagram with separated, locally of finite
type, locally quasi-finite vertical maps, the canonical map from the upper pushout to the
lower pushout is locally quasi-finite. -/
instance instPushoutMapLocallyQuasiFinite {S : Scheme.{u}} {Z X Y : Over S}
    {Z' X' Y' : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    (i' : Z' ⟶ X') (j' : Z' ⟶ Y') (f : X' ⟶ X.left)
    (g : Y' ⟶ Y.left) (h : Z' ⟶ Z.left) [IsAdmissibleSpan i j]
    [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated g] [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    [IsSeparated h] [LocallyOfFiniteType h] [LocallyQuasiFinite h]
    (hX : IsPullback i' h f i.left) (hY : IsPullback j' h g j.left)
    [HasPushout i' j'] :
    LocallyQuasiFinite
      (pushout.map i' j' i.left j.left f g h hX.w hY.w) := sorry

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
