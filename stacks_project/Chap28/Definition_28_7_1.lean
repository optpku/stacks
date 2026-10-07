module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
import StacksCheckRecall

@[expose] public section

universe u

/-!
Compatibility entry for Definition 28.7.1. The reusable owner is
`ReasLib.AlgebraicGeometry.Scheme.Normal`.
-/

/- Definition 28.7.1: a scheme is normal when its local rings are normal domains. -/
@[stacks 033I]
#check (AlgebraicGeometry.Scheme.isNormal : AlgebraicGeometry.Scheme.{u} → Prop)

#check (AlgebraicGeometry.Scheme.isNormalAt :
  ∀ X : AlgebraicGeometry.Scheme.{u}, X → Prop)

#check (AlgebraicGeometry.Scheme.isNormalAt_iff :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (x : X),
    X.isNormalAt x ↔ IsNormalRing (X.presheaf.stalk x))

#check (AlgebraicGeometry.Scheme.isNormalAt.isNormalRing :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) {x : X},
    X.isNormalAt x → IsNormalRing (X.presheaf.stalk x))

#check (AlgebraicGeometry.Scheme.isNormalAt.isReduced :
  ∀ {Y : AlgebraicGeometry.Scheme.{u}} {y : Y},
    Y.isNormalAt y → _root_.IsReduced (Y.presheaf.stalk y))

#check (AlgebraicGeometry.Scheme.isNormal_def :
  ∀ X : AlgebraicGeometry.Scheme.{u}, X.isNormal ↔ ∀ x : X, X.isNormalAt x)

#check (AlgebraicGeometry.Scheme.isNormal.isNormalAt :
  ∀ X : AlgebraicGeometry.Scheme.{u}, X.isNormal → ∀ x : X, X.isNormalAt x)

#check (AlgebraicGeometry.Scheme.isNormal.isNormalRing_stalk :
  ∀ X : AlgebraicGeometry.Scheme.{u}, X.isNormal →
    ∀ x : X, IsNormalRing (X.presheaf.stalk x))

#check (AlgebraicGeometry.Scheme.isNormal_iff :
  ∀ X : AlgebraicGeometry.Scheme.{u},
    X.isNormal ↔ ∀ x : X, IsNormalRing (X.presheaf.stalk x))

#check (AlgebraicGeometry.Scheme.isReduced_of_isNormal :
  ∀ {Y : AlgebraicGeometry.Scheme.{u}},
    Y.isNormal → AlgebraicGeometry.IsReduced Y)
