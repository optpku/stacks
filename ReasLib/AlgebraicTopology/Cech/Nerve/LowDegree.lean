/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicTopology.Cech.Nerve.Projection

/-!
@stack 016E

# Low degrees of a Cech nerve

The degree-zero term of a Cech nerve is canonically isomorphic to the source of the arrow,
while its degree-one term is a pullback of the arrow along itself.  The limit cone is exposed
without requiring a separately chosen binary pullback; a comparison with mathlib's chosen
`pullback` is provided only when that choice is already available.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

namespace cechNerve.degreeZero

variable (f : Arrow C) [f.HasCechNerve]

/-- The identity family satisfies the compatibility condition defining degree zero of the Cech
nerve. -/
@[stacks 016E "degree-zero Cech-nerve inverse compatibility"]
theorem inv_condition :
    forall _ : Fin 1, (𝟙 f.left : f.left ⟶ f.left) ≫ f.hom = f.hom := sorry

/-- The canonical map from the source of an arrow to degree zero of its Cech nerve. -/
@[stacks 016E "degree-zero Cech-nerve inverse"]
noncomputable def inv : f.left ⟶ f.cechNerve.obj (op ⦋0⦌) :=
  cechNerve.lift f (op ⦋0⦌) f.hom (fun _ ↦ 𝟙 f.left) (inv_condition f)

/-- The degree-zero projection followed by the canonical inverse is the identity. -/
@[reassoc (attr := simp), stacks 016E "degree-zero Cech-nerve projection-inverse identity"]
theorem projection_comp_inv :
    cechNerve.π f (op ⦋0⦌) 0 ≫ inv f = 𝟙 (f.cechNerve.obj (op ⦋0⦌)) := sorry

/-- The canonical inverse followed by the degree-zero projection is the identity. -/
@[reassoc (attr := simp), stacks 016E "degree-zero Cech-nerve inverse-projection identity"]
theorem inv_π : inv f ≫ cechNerve.π f (op ⦋0⦌) 0 = 𝟙 f.left := sorry

/-- The canonical inverse has the expected composite with the base projection. -/
@[reassoc (attr := simp), stacks 016E "degree-zero Cech-nerve inverse base computation"]
theorem inv_base : inv f ≫ cechNerve.base f (op ⦋0⦌) = f.hom := sorry

/-- The canonical identification of degree zero of a Cech nerve with the source of its arrow. -/
@[stacks 016E "degree-zero Cech-nerve identification"]
noncomputable def iso : f.cechNerve.obj (op ⦋0⦌) ≅ f.left where
  hom := cechNerve.π f (op ⦋0⦌) 0
  inv := inv f
  hom_inv_id := projection_comp_inv f
  inv_hom_id := inv_π f

/-- The forward map of the degree-zero identification is the unique vertex projection. -/
@[simp, stacks 016E "degree-zero Cech-nerve identification forward map"]
theorem iso_hom : (iso f).hom = cechNerve.π f (op ⦋0⦌) 0 := sorry

/-- The inverse map of the degree-zero identification is the canonical Cech-nerve lift. -/
@[simp, stacks 016E "degree-zero Cech-nerve identification inverse map"]
theorem iso_inv : (iso f).inv = inv f := sorry

end cechNerve.degreeZero

namespace cechNerve.degreeOne

variable (f : Arrow C) [f.HasCechNerve]

/-- The first projection from degree one of a Cech nerve. -/
@[stacks 016E "degree-one Cech-nerve first projection"]
noncomputable def fst : f.cechNerve.obj (op ⦋1⦌) ⟶ f.left :=
  cechNerve.π f (op ⦋1⦌) 0

/-- The second projection from degree one of a Cech nerve. -/
@[stacks 016E "degree-one Cech-nerve second projection"]
noncomputable def snd : f.cechNerve.obj (op ⦋1⦌) ⟶ f.left :=
  cechNerve.π f (op ⦋1⦌) 1

/-- The two degree-one projections have equal composites with the underlying arrow. -/
@[reassoc, stacks 016E "degree-one Cech-nerve pullback condition"]
theorem condition : fst f ≫ f.hom = snd f ≫ f.hom := sorry

/-- Two compatible maps to the source define a compatible family indexed by the two vertices. -/
@[stacks 016E "degree-one Cech-nerve lift compatibility"]
theorem lift_condition {Z : C} (a b : Z ⟶ f.left)
    (w : a ≫ f.hom = b ≫ f.hom) :
    forall i : Fin 2, Fin.cases a (fun _ ↦ b) i ≫ f.hom = a ≫ f.hom := sorry

/-- The pullback-style lift used to assemble the degree-one limit cone. -/
@[stacks 016E "degree-one Cech-nerve pullback lift"]
noncomputable def lift {Z : C} (a b : Z ⟶ f.left)
    (w : a ≫ f.hom = b ≫ f.hom) :
    Z ⟶ f.cechNerve.obj (op ⦋1⦌) :=
  cechNerve.lift f (op ⦋1⦌) (a ≫ f.hom) (Fin.cases a (fun _ ↦ b))
    (lift_condition f a b w)

/-- The internal degree-one lift has the prescribed first projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve lift first projection"]
theorem lift_fst {Z : C} (a b : Z ⟶ f.left)
    (w : a ≫ f.hom = b ≫ f.hom) :
    lift f a b w ≫ fst f = a := sorry

/-- The internal degree-one lift has the prescribed second projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve lift second projection"]
theorem lift_snd {Z : C} (a b : Z ⟶ f.left)
    (w : a ≫ f.hom = b ≫ f.hom) :
    lift f a b w ≫ snd f = b := sorry

/-- The internal degree-one lift is unique among maps with the prescribed projections. -/
@[stacks 016E "degree-one Cech-nerve lift uniqueness"]
theorem lift_unique {Z : C} (a b : Z ⟶ f.left)
    (w : a ≫ f.hom = b ≫ f.hom)
    (m : Z ⟶ f.cechNerve.obj (op ⦋1⦌))
    (hfst : m ≫ fst f = a) (hsnd : m ≫ snd f = b) :
    m = lift f a b w := sorry

/-- Degree one of a Cech nerve, equipped with its two projections, as a pullback cone. -/
@[stacks 016E "degree-one Cech-nerve pullback cone"]
noncomputable def cone : PullbackCone f.hom f.hom :=
  PullbackCone.mk (fst f) (snd f) (condition f)

/-- The point of the degree-one pullback cone is degree one of the Cech nerve. -/
@[simp, stacks 016E "degree-one Cech-nerve pullback cone point"]
theorem cone_pt : (cone f).pt = f.cechNerve.obj (op ⦋1⦌) := sorry

/-- The first leg of the degree-one pullback cone is the first vertex projection. -/
@[simp, stacks 016E "degree-one Cech-nerve pullback cone first leg"]
theorem cone_fst : (cone f).fst = fst f := sorry

/-- The second leg of the degree-one pullback cone is the second vertex projection. -/
@[simp, stacks 016E "degree-one Cech-nerve pullback cone second leg"]
theorem cone_snd : (cone f).snd = snd f := sorry

/-- Degree one of a Cech nerve is a pullback of the underlying arrow along itself. -/
@[stacks 016E "degree-one Cech-nerve pullback universal property"]
noncomputable def isLimit : IsLimit (cone f) :=
  PullbackCone.IsLimit.mk (condition f)
    (fun s ↦ lift f s.fst s.snd s.condition)
    (fun s ↦ lift_fst f s.fst s.snd s.condition)
    (fun s ↦ lift_snd f s.fst s.snd s.condition)
    (fun s m hfst hsnd ↦ lift_unique f s.fst s.snd s.condition m hfst hsnd)

/-- The comparison from degree one of a Cech nerve to mathlib's chosen pullback. -/
@[stacks 016E "degree-one Cech-nerve chosen-pullback comparison"]
noncomputable def pullbackIso [HasPullback f.hom f.hom] :
    f.cechNerve.obj (op ⦋1⦌) ≅ pullback f.hom f.hom :=
  (limit.isoLimitCone ⟨cone f, isLimit f⟩).symm

namespace pullbackIso

variable [HasPullback f.hom f.hom]

/-- The chosen-pullback comparison preserves the first projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve comparison first projection"]
theorem hom_fst :
    (pullbackIso f).hom ≫ pullback.fst f.hom f.hom = fst f := sorry

/-- The chosen-pullback comparison preserves the second projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve comparison second projection"]
theorem hom_snd :
    (pullbackIso f).hom ≫ pullback.snd f.hom f.hom = snd f := sorry

/-- The inverse chosen-pullback comparison preserves the first projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve inverse comparison first projection"]
theorem inv_fst :
    (pullbackIso f).inv ≫ fst f = pullback.fst f.hom f.hom := sorry

/-- The inverse chosen-pullback comparison preserves the second projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve inverse comparison second projection"]
theorem inv_snd :
    (pullbackIso f).inv ≫ snd f = pullback.snd f.hom f.hom := sorry

end pullbackIso

/-- The zeroth face map is the second projection after identifying degree zero with the arrow
source. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve zeroth face"]
theorem face_zero_iso_hom :
    f.cechNerve.δ (0 : Fin 2) ≫ (cechNerve.degreeZero.iso f).hom = snd f := sorry

/-- The first face map is the first projection after identifying degree zero with the arrow
source. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve first face"]
theorem face_one_iso_hom :
    f.cechNerve.δ (1 : Fin 2) ≫ (cechNerve.degreeZero.iso f).hom = fst f := sorry

/-- The second projection followed by the inverse degree-zero identification recovers the
zeroth face map. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve zeroth face inverse formula"]
theorem snd_iso_inv :
    snd f ≫ (cechNerve.degreeZero.iso f).inv =
      f.cechNerve.δ (0 : Fin 2) := sorry

/-- The first projection followed by the inverse degree-zero identification recovers the first
face map. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve first face inverse formula"]
theorem fst_iso_inv :
    fst f ≫ (cechNerve.degreeZero.iso f).inv =
      f.cechNerve.δ (1 : Fin 2) := sorry

/-- The degree-zero degeneracy, transported from the arrow source, is the diagonal into degree
one. -/
@[stacks 016E "degree-one Cech-nerve diagonal"]
noncomputable def diagonal : f.left ⟶ f.cechNerve.obj (op ⦋1⦌) :=
  (cechNerve.degreeZero.iso f).inv ≫ f.cechNerve.σ (0 : Fin 1)

/-- The diagonal into degree one has identity first projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve diagonal first projection"]
theorem diagonal_fst : diagonal f ≫ fst f = 𝟙 f.left := sorry

/-- The diagonal into degree one has identity second projection. -/
@[reassoc (attr := simp), stacks 016E "degree-one Cech-nerve diagonal second projection"]
theorem diagonal_snd : diagonal f ≫ snd f = 𝟙 f.left := sorry

end cechNerve.degreeOne

end CategoryTheory.Arrow
