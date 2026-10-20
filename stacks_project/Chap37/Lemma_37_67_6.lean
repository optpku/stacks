module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable {S : AlgebraicGeometry.Scheme.{u}}
  {Z X Y : Over S} {Z' X' Y' : AlgebraicGeometry.Scheme.{u}}
  (i : Z ⟶ X) (j : Z ⟶ Y) (i' : Z' ⟶ X') (j' : Z' ⟶ Y')
  (f : X' ⟶ X.left) (g : Y' ⟶ Y.left) (h : Z' ⟶ Z.left)
  [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j]
  [AlgebraicGeometry.IsSeparated f] [AlgebraicGeometry.LocallyOfFiniteType f]
  [AlgebraicGeometry.LocallyQuasiFinite f]
  [AlgebraicGeometry.IsSeparated g] [AlgebraicGeometry.LocallyOfFiniteType g]
  [AlgebraicGeometry.LocallyQuasiFinite g]
  [AlgebraicGeometry.IsSeparated h] [AlgebraicGeometry.LocallyOfFiniteType h]
  [AlgebraicGeometry.LocallyQuasiFinite h]
  (hX : IsPullback i' h f i.left) (hY : IsPullback j' h g j.left)

/- Lemma 37.67.6: a cartesian morphism to an admissible span, whose vertical maps are
separated and locally quasi-finite, induces an upper pushout. -/
@[stacks 0ECK] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.hasPushoutOfBaseChange
    i j i' j' f g h hX hY : HasPushout i' j')

#check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instHasPushout i j :
    HasPushout i.left j.left)

variable [HasPushout i' j']

#check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instPushoutMapIsSeparated
    i j i' j' f g h hX hY :
    AlgebraicGeometry.IsSeparated
      (pushout.map i' j' i.left j.left f g h hX.w hY.w))

#check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instPushoutMapLocallyOfFiniteType
    i j i' j' f g h hX hY :
    AlgebraicGeometry.LocallyOfFiniteType
      (pushout.map i' j' i.left j.left f g h hX.w hY.w))

#check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instPushoutMapLocallyQuasiFinite
    i j i' j' f g h hX hY :
    AlgebraicGeometry.LocallyQuasiFinite
      (pushout.map i' j' i.left j.left f g h hX.w hY.w))

#check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.baseChangeInr_isPullback
    i j i' j' f g h hX hY :
    IsPullback (pushout.inr i' j') g
      (pushout.map i' j' i.left j.left f g h hX.w hY.w)
      (pushout.inr i.left j.left))

#check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.baseChangeInl_isPullback
    i j i' j' f g h hX hY :
    IsPullback (pushout.inl i' j') f
      (pushout.map i' j' i.left j.left f g h hX.w hY.w)
      (pushout.inl i.left j.left))
