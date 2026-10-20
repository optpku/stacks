module

public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
import StacksCheckRecall

/-!
# Definition 28.4.2

The reusable owner `Scheme.HasRingPropertyLocally` lives in
`ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic`.  This chapter file
is a compatibility entry point for the textbook item.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Definition 28.4.2: the affine-local ring-property predicate on schemes. -/
@[stacks 01OQ] #check (AlgebraicGeometry.Scheme.HasRingPropertyLocally :
  AlgebraicGeometry.Scheme.{u} → (CommRingCat.{u} → Prop) → Prop)

#check (AlgebraicGeometry.Scheme.instMembershipAffineOpens :
  ∀ X : AlgebraicGeometry.Scheme.{u}, Membership X X.affineOpens)

#check (AlgebraicGeometry.Scheme.HasRingPropertyLocally.exists_affineOpen :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (P : CommRingCat.{u} → Prop)
    [X.HasRingPropertyLocally P] (x : X),
    ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U)))

#check (AlgebraicGeometry.Scheme.hasRingPropertyLocally_iff :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (P : CommRingCat.{u} → Prop),
    X.HasRingPropertyLocally P ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ P (Γ(X, U)))
