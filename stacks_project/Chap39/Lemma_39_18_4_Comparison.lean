module

public import stacks_project.Chap39.Definition_39_13_1_GroupoidScheme
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

/-!
# Comparison of the two groupoid-scheme interfaces

This module regards a `GroupoidScheme` as a `Scheme.Groupoid` so Chapter 39 can reuse the
canonical `Scheme.Groupoid` stabilizer API.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Regard a pointwise `GroupoidScheme` as a diagrammatic `Scheme.Groupoid`. -/
def toGroupoid {S : Scheme.{u}} (G : GroupoidScheme S) : Scheme.Groupoid S where
  U := G.U
  R := G.R
  s := G.s
  t := G.t
  c := G.c
  e := G.e
  i := G.i
  comp_source := G.comp_source
  comp_target := G.comp_target
  identity_source := G.identity_source
  identity_target := G.identity_target
  inverse_source := G.inverse_source
  inverse_target := G.inverse_target
  associativity := G.associativity
  right_identity := G.right_identity
  left_identity := G.left_identity
  inverse_comp := G.inverse_comp
  comp_inverse := G.comp_inverse

/-- The comparison preserves the object scheme. -/
@[simp] theorem toGroupoid_U {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toGroupoid.U = G.U := rfl

/-- The comparison preserves the arrow scheme. -/
@[simp] theorem toGroupoid_R {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toGroupoid.R = G.R := rfl

/-- The comparison preserves the source map. -/
@[simp] theorem toGroupoid_s {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toGroupoid.s = G.s := rfl

/-- The comparison preserves the target map. -/
@[simp] theorem toGroupoid_t {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toGroupoid.t = G.t := rfl

/-- The comparison preserves the underlying pre-relation. -/
@[simp] theorem toGroupoid_toPreRelation {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toGroupoid.toPreRelation = G.toPreRelation := rfl

end AlgebraicGeometry.GroupoidScheme
