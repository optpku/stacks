module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cleavages on categorical-pullback projections

A cleavage on `p : S ⥤ D` induces a cleavage on the first projection
`CategoricalPullback.π₁ u p : u ⊡ p ⥤ C`.  The construction is explicit: a lift of
`f : V ⟶ x.fst` uses the selected lift under `p` of
`u.map f ≫ x.iso.hom`.

Keeping the induced cleavage as data is stronger than merely proving that the pullback projection
is fibred.  In particular, later comparison maps between the fibers of `π₁ u p` and the fibers of
`p` can refer to the same selected cartesian arrows instead of comparing two unrelated global
choices.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The base arrow in `D` whose selected lift supplies a lift for the first projection of a
categorical pullback. -/
@[stacks 04WB "induced categorical-pullback lift base map"]
def Cleavage.liftBaseMap (u : C ⥤ D) (p : S ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    u.obj V ⟶ p.obj x.snd :=
  u.map f ≫ x.iso.hom

/-- The source object in the categorical pullback of the lift induced from a cleavage on the
right leg. -/
@[stacks 04WB "induced categorical-pullback lift source"]
def Cleavage.liftSource {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    u ⊡ p :=
  let l := χ.lift (Cleavage.liftBaseMap u p f)
  { fst := V
    snd := l.source
    iso := eqToIso l.sourceObj.symm }

/-- Compatibility of the two components of the categorical-pullback lift induced from a
cleavage. -/
@[stacks 04WB "induced categorical-pullback lift compatibility"]
theorem Cleavage.liftCompatibility {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    u.map f ≫ x.iso.hom =
      (Cleavage.liftSource χ u f).iso.hom ≫
        p.map (χ.lift (Cleavage.liftBaseMap u p f)).hom := sorry

/-- The categorical-pullback arrow underlying the lift induced from a cleavage on the right
leg. -/
@[stacks 04WB "induced categorical-pullback lift arrow"]
def Cleavage.liftHom {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    Cleavage.liftSource χ u f ⟶ x where
  fst := f
  snd := (χ.lift (Cleavage.liftBaseMap u p f)).hom
  w := Cleavage.liftCompatibility χ u f

/-- The induced lift is strongly cartesian for the first projection of the categorical
pullback. -/
@[stacks 04WB "cartesianness of the induced categorical-pullback lift"]
theorem Cleavage.liftHom.isStronglyCartesian
    {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    (π₁ u p).IsStronglyCartesian f (Cleavage.liftHom χ u f) := sorry

/-- The strongly cartesian lift for the first projection induced by a cleavage on the right
leg. -/
@[stacks 04WB "induced categorical-pullback cartesian lift"]
def Cleavage.lift {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    StronglyCartesianLift (π₁ u p) f where
  source := Cleavage.liftSource χ u f
  hom := Cleavage.liftHom χ u f
  isStronglyCartesian := Cleavage.liftHom.isStronglyCartesian χ u f

/-- The first component of the source of an induced lift is the requested base object. -/
@[simp, stacks 04WB "induced lift source first-component readout"]
theorem Cleavage.liftSource.fst
    {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    (Cleavage.liftSource χ u f).fst = V := sorry

/-- The second component of the source of an induced lift is the source selected by the original
cleavage. -/
@[simp, stacks 04WB "induced lift source second-component readout"]
theorem Cleavage.liftSource.snd
    {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    (Cleavage.liftSource χ u f).snd =
      (χ.lift (Cleavage.liftBaseMap u p f)).source := sorry

/-- The first component of an induced cartesian arrow is the original base arrow. -/
@[simp, stacks 04WB "induced lift arrow first-component readout"]
theorem Cleavage.liftHom.fst
    {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    (Cleavage.liftHom χ u f).fst = f := sorry

/-- The second component of an induced cartesian arrow is the selected cartesian arrow for the
right leg. -/
@[simp, stacks 04WB "induced lift arrow second-component readout"]
theorem Cleavage.liftHom.snd
    {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D)
    {x : u ⊡ p} {V : C} (f : V ⟶ x.fst) :
    (Cleavage.liftHom χ u f).snd =
      (χ.lift (Cleavage.liftBaseMap u p f)).hom := sorry

end Limits.CategoricalPullback

namespace Functor.Cleavage

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- A cleavage on the right leg of a categorical pullback induces a cleavage on its first
projection. -/
@[stacks 04WB "induced cleavage on a categorical-pullback projection"]
def ofRight {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D) :
    (π₁ u p).Cleavage where
  lift f := Limits.CategoricalPullback.Cleavage.lift χ u f

/-- Lemma 8.12.1 (tag 04WB): the induced cleavage exhibits the first projection of a
categorical pullback as fibred. -/
@[stacks 04WB "fibredness from an explicit right-leg cleavage"]
theorem ofRight.isFibered
    {p : S ⥤ D} (χ : p.Cleavage) (u : C ⥤ D) :
    (π₁ u p).IsFibered := sorry

end Functor.Cleavage

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The cleavage on a categorical-pullback projection induced from mathlib's selected cleavage on
the right leg. -/
@[stacks 04WB "canonical cleavage on a categorical-pullback projection"]
noncomputable def Cleavage.chosen
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] :
    (π₁ u p).Cleavage :=
  (Functor.Cleavage.ofIsFibered p).ofRight u

/-- The object selected by the induced pullback cleavage when the right leg carries mathlib's
chosen cleavage. -/
@[stacks 04WB "chosen categorical-pullback reindexing object"]
noncomputable def Cleavage.chosen.reindexObj
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (π₁ u p).Fiber V :=
  (Cleavage.chosen u p).reindexObj f X

/-- The cartesian arrow selected by the induced pullback cleavage when the right leg carries
mathlib's chosen cleavage. -/
@[stacks 04WB "chosen categorical-pullback cartesian arrow"]
noncomputable def Cleavage.chosen.cartesianHom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (Cleavage.chosen.reindexObj u p f X).1 ⟶ X.1 :=
  (Cleavage.chosen u p).cartesianHom f X

/-- The morphism selected by induced pullback reindexing. -/
@[stacks 04WB "chosen categorical-pullback reindexing map"]
noncomputable def Cleavage.chosen.reindexMap
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {X Y : (π₁ u p).Fiber U}
    (φ : X ⟶ Y) :
    Cleavage.chosen.reindexObj u p f X ⟶
      Cleavage.chosen.reindexObj u p f Y :=
  (Cleavage.chosen u p).reindexMap f φ

/-- Reindexing for the first pullback projection induced from mathlib's chosen cleavage on the
right leg.  Unlike `Cleavage.ofIsFibered (π₁ u p)`, this remembers its construction from the
right-leg cleavage and therefore supports canonical base-change comparisons. -/
@[stacks 04WB "chosen categorical-pullback reindexing functor"]
noncomputable def Cleavage.chosen.reindex
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) :
    (π₁ u p).Fiber U ⥤ (π₁ u p).Fiber V :=
  (Cleavage.chosen u p).reindex f

/-- Objectwise computation for reindexing by the induced selected pullback cleavage. -/
@[simp, stacks 04WB "chosen pullback reindexing object readout"]
theorem Cleavage.chosen.reindex.obj
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (Cleavage.chosen.reindex u p f).obj X =
      Cleavage.chosen.reindexObj u p f X := sorry

/-- Morphismwise computation for reindexing by the induced selected pullback cleavage. -/
@[simp, stacks 04WB "chosen pullback reindexing map readout"]
theorem Cleavage.chosen.reindex.map
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {X Y : (π₁ u p).Fiber U}
    (φ : X ⟶ Y) :
    (Cleavage.chosen.reindex u p f).map φ =
      Cleavage.chosen.reindexMap u p f φ := sorry

/-- The selected induced reindexing map is characterized by cartesian factorization. -/
@[reassoc, stacks 04WB "chosen pullback reindexing factorization"]
theorem Cleavage.chosen.reindexMap.fac
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {X Y : (π₁ u p).Fiber U}
    (φ : X ⟶ Y) :
    (Cleavage.chosen.reindexMap u p f φ).1 ≫
        Cleavage.chosen.cartesianHom u p f Y =
      Cleavage.chosen.cartesianHom u p f X ≫ φ.1 := sorry

/-- The selected cartesian arrow is strongly cartesian for the first pullback projection. -/
@[stacks 04WB "chosen pullback reindexing cartesianness"]
instance Cleavage.chosen.cartesianHom.isStronglyCartesian
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (X : (π₁ u p).Fiber U) :
    (π₁ u p).IsStronglyCartesian f
      (Cleavage.chosen.cartesianHom u p f X) := sorry

namespace Left

/-- Lemma 8.12.1 (tag 04WB): base change of a fibred projection along an arbitrary functor is
again fibred.  This is the canonical, cleavage-independent owner used by downstream code. -/
@[stacks 04WB]
instance isFibered (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] :
    (π₁ u p).IsFibered := sorry

end Left

end Limits.CategoricalPullback

end CategoryTheory

/- Data audit (mathlib 4.32): the explicit and chosen cleavages retain the selected source and
cartesian arrow as concrete data.  The reindexing object, arrow, map, and functor are projections
of that same cleavage, rather than fresh choices.  Any `sorryAx` reported here is confined to the
cartesianness and factorization laws stored with the canonical data owners. -/
