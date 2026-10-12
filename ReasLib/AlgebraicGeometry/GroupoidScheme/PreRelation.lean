/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Hom

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The pre-relation induced by the target-source morphism of a groupoid scheme is a
pre-equivalence relation on points over the base scheme. -/
theorem toPreRelation_isPreEquivalence {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.IsPreEquivalence := by
  intro T
  -- Rewrite the induced point relation into the explicit arrow-witness form.
  have pointRel_iff {x y : T ⟶ G.U} :
      G.toPreRelation.pointRel T x y ↔
        ∃ r : T ⟶ G.R, r ≫ G.t = x ∧ r ≫ G.s = y := by
    -- Expose the witness relation first, then normalize the hidden source object and projections.
    change (∃ r : T ⟶ G.toPreRelation.left, r ≫ G.toPreRelation.t = x ∧ r ≫ G.toPreRelation.s = y) ↔
        ∃ r : T ⟶ G.R, r ≫ G.t = x ∧ r ≫ G.s = y
    rw [G.toPreRelation_t, G.toPreRelation_s]
    change (∃ r : T ⟶ G.R, r ≫ G.t = x ∧ r ≫ G.s = y) ↔
        ∃ r : T ⟶ G.R, r ≫ G.t = x ∧ r ≫ G.s = y
    exact Iff.rfl
  constructor
  · intro x
    -- Reflexivity is witnessed by the identity arrow at `x`.
    rw [pointRel_iff]
    refine ⟨x ≫ G.e, ?_, ?_⟩
    · calc
        (x ≫ G.e) ≫ G.t = x ≫ (G.e ≫ G.t) := by rw [Category.assoc]
        _ = x ≫ 𝟙 G.U := by rw [G.identity_target]
        _ = x := by simp
    · calc
        (x ≫ G.e) ≫ G.s = x ≫ (G.e ≫ G.s) := by rw [Category.assoc]
        _ = x ≫ 𝟙 G.U := by rw [G.identity_source]
        _ = x := by simp
  · intro x y hxy
    -- Symmetry is witnessed by sending an arrow to its inverse.
    rw [pointRel_iff] at hxy ⊢
    rcases hxy with ⟨r, hr_target, hr_source⟩
    refine ⟨r ≫ G.i, ?_, ?_⟩
    · calc
        (r ≫ G.i) ≫ G.t = r ≫ (G.i ≫ G.t) := by rw [Category.assoc]
        _ = r ≫ G.s := by rw [G.inverse_target]
        _ = y := hr_source
    · calc
        (r ≫ G.i) ≫ G.s = r ≫ (G.i ≫ G.s) := by rw [Category.assoc]
        _ = r ≫ G.t := by rw [G.inverse_source]
        _ = x := hr_target
  · intro x y z hxy hyz
    -- Transitivity is witnessed by composing compatible arrows.
    rw [pointRel_iff] at hxy hyz ⊢
    rcases hxy with ⟨rxy, hrxy_target, hrxy_source⟩
    rcases hyz with ⟨ryz, hryz_target, hryz_source⟩
    have hcomp : rxy ≫ G.s = ryz ≫ G.t := hrxy_source.trans hryz_target.symm
    refine ⟨G.compose rxy ryz hcomp, ?_, ?_⟩
    · calc
        G.compose rxy ryz hcomp ≫ G.t = rxy ≫ G.t := G.compose_target rxy ryz hcomp
        _ = x := hrxy_target
    · calc
        G.compose rxy ryz hcomp ≫ G.s = ryz ≫ G.s := G.compose_source rxy ryz hcomp
        _ = z := hryz_source

namespace Hom

/-- The morphism of pre-relations induced by a morphism of groupoid schemes. -/
def toPreRelation {S : Scheme.{u}} {G G' : GroupoidScheme S} (f : Hom G G') :
    Scheme.PreRelation.Hom G.toPreRelation G'.toPreRelation where
  obj := f.obj
  arrow := f.arrow
  map_s := by
    rw [GroupoidScheme.toPreRelation_s, GroupoidScheme.toPreRelation_s]
    exact f.map_s
  map_t := by
    rw [GroupoidScheme.toPreRelation_t, GroupoidScheme.toPreRelation_t]
    exact f.map_t

/-- The object map of the induced pre-relation morphism is the original object map. -/
@[simp] theorem toPreRelation_obj {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (f : Hom G G') : f.toPreRelation.obj = f.obj := rfl

/-- The arrow map of the induced pre-relation morphism is the original arrow map. -/
@[simp] theorem toPreRelation_arrow {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (f : Hom G G') : f.toPreRelation.arrow = f.arrow := rfl

end Hom

end AlgebraicGeometry.GroupoidScheme
