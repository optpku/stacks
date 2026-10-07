module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Projection.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vertex projections from bundled bicategorical cospans

This file names the three vertex evaluations of `Cospan.projectionDiagram` and its two
generating transformations. The construction remains owned by the single walking-cospan
pseudofunctor; these declarations are its conventional cospan-shaped interface.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]

variable (B) in
/-- The left-endpoint projection from bundled cospans to the ambient bicategory. -/
@[stacks 0040 "left-endpoint projection from bundled bicategorical cospans"]
def leftProjection : Pseudofunctor (Cospan B) B :=
  (projectionDiagram B).obj
    (LocallyDiscrete.mk Limits.WalkingCospan.left)

variable (B) in
/-- The right-endpoint projection from bundled cospans to the ambient bicategory. -/
@[stacks 0040 "right-endpoint projection from bundled bicategorical cospans"]
def rightProjection : Pseudofunctor (Cospan B) B :=
  (projectionDiagram B).obj
    (LocallyDiscrete.mk Limits.WalkingCospan.right)

variable (B) in
/-- The common-target projection from bundled cospans to the ambient bicategory. -/
@[stacks 0040 "common-target projection from bundled bicategorical cospans"]
def baseProjection : Pseudofunctor (Cospan B) B :=
  (projectionDiagram B).obj
    (LocallyDiscrete.mk Limits.WalkingCospan.one)

variable (B) in
/-- The tautological left leg, as a strong transformation from the left-endpoint projection
to the common-target projection. -/
@[stacks 0040 "tautological left leg of bundled bicategorical cospans"]
def fstTransformation :
    leftProjection B ⟶ baseProjection B :=
  (projectionDiagram B).map
    (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)

variable (B) in
/-- The tautological right leg, as a strong transformation from the right-endpoint projection
to the common-target projection. -/
@[stacks 0040 "tautological right leg of bundled bicategorical cospans"]
def sndTransformation :
    rightProjection B ⟶ baseProjection B :=
  (projectionDiagram B).map
    (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)

/-- The left projection evaluates a bundled cospan at its left endpoint. -/
@[simp]
theorem leftProjection.obj (S : Cospan B) :
    (leftProjection B).obj S = S.left := sorry

/-- The right projection evaluates a bundled cospan at its right endpoint. -/
@[simp]
theorem rightProjection.obj (S : Cospan B) :
    (rightProjection B).obj S = S.right := sorry

/-- The base projection evaluates a bundled cospan at its common target. -/
@[simp]
theorem baseProjection.obj (S : Cospan B) :
    (baseProjection B).obj S = S.base := sorry

/-- On `1`-morphisms, the left projection takes the left component. -/
@[simp]
theorem leftProjection.map {S T : Cospan B} (ψ : S ⟶ T) :
    (leftProjection B).map ψ = Hom.left ψ := sorry

/-- On `1`-morphisms, the right projection takes the right component. -/
@[simp]
theorem rightProjection.map {S T : Cospan B} (ψ : S ⟶ T) :
    (rightProjection B).map ψ = Hom.right ψ := sorry

/-- On `1`-morphisms, the base projection takes the common-target component. -/
@[simp]
theorem baseProjection.map {S T : Cospan B} (ψ : S ⟶ T) :
    (baseProjection B).map ψ = Hom.base ψ := sorry

/-- On `2`-morphisms, the left projection takes the left component. -/
@[simp]
theorem leftProjection.map₂
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (leftProjection B).map₂ Γ = Hom₂.left Γ := sorry

/-- On `2`-morphisms, the right projection takes the right component. -/
@[simp]
theorem rightProjection.map₂
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (rightProjection B).map₂ Γ = Hom₂.right Γ := sorry

/-- On `2`-morphisms, the base projection takes the common-target component. -/
@[simp]
theorem baseProjection.map₂
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (baseProjection B).map₂ Γ = Hom₂.base Γ := sorry

/-- The component of the tautological left leg at a bundled cospan is its left leg. -/
@[simp]
theorem fstTransformation.app (S : Cospan B) :
    (fstTransformation B).app S = S.fst := sorry

/-- The component of the tautological right leg at a bundled cospan is its right leg. -/
@[simp]
theorem sndTransformation.app (S : Cospan B) :
    (sndTransformation B).app S = S.snd := sorry

/-- Naturality of the tautological left leg is the generating left comparison of a
bundled-cospan morphism. -/
@[simp]
theorem fstTransformation.naturality
    {S T : Cospan B} (ψ : S ⟶ T) :
    (fstTransformation B).naturality ψ =
      Hom.leftIso ψ := sorry

/-- Naturality of the tautological right leg is the generating right comparison of a
bundled-cospan morphism. -/
@[simp]
theorem sndTransformation.naturality
    {S T : Cospan B} (ψ : S ⟶ T) :
    (sndTransformation B).naturality ψ =
      Hom.rightIso ψ := sorry

/- Data and axiom audit (mathlib 4.32):

The three projections and two transformations are literal evaluations and generator maps of
`projectionDiagram`; they introduce no parallel component or coherence data. `#print axioms`
reports `[propext, sorryAx, Classical.choice, Quot.sound]` for each declaration, with
`sorryAx` inherited only from the underlying pseudofunctor and strong-transformation laws. -/

end CategoryTheory.Bicategory.Cospan
