/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Intrinsic reindexing for discrete fibrations

The unique lift of a discrete fibration determines strict reindexing on standard fiber objects.
This file exposes its object, cartesian-arrow, uniqueness, identity, and composition API.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsDiscreteFibration

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- The intrinsic reindexing object of `x` along `f`, obtained directly from the unique lift in a
discrete fibration. Unlike a general cleavage reindexing, this object is canonical by strict
uniqueness rather than merely canonical up to isomorphism. -/
@[stacks 0043 "intrinsic reindexing object"]
noncomputable def reindexObj
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.Fiber V :=
  let l := lift p (f ≫ eqToHom x.2.symm)
  ⟨l.domain, @IsHomLift.domain_eq _ _ _ _ p _ _ _ _ (f ≫ eqToHom x.2.symm) l.hom l.isHomLift⟩

/-- The intrinsic cartesian arrow from the reindexed object to the original fiber object. -/
@[stacks 0043 "intrinsic reindexing arrow"]
noncomputable def cartesianHom
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (reindexObj p f x).1 ⟶ x.1 :=
  (lift p (f ≫ eqToHom x.2.symm)).hom

/- Axiom audit: `reindexObj` and `cartesianHom` project the domain and morphism of `lift`; their
non-`Prop` payload therefore depends only on `Classical.choice`. The fiber-membership witness of
`reindexObj` is the proved mathlib theorem `IsHomLift.domain_eq`. -/

/-- The underlying object of intrinsic reindexing is the domain of the selected lift. -/
@[simp]
theorem reindexObj.val
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    (reindexObj p f x).1 =
      (lift p (f ≫ eqToHom x.2.symm)).domain := sorry
/- Proof strategy: unfold `reindexObj`; the first projection is definitionally the lift domain. -/

/-- The intrinsic reindexing object lies over the source of the base morphism. -/
@[simp]
theorem reindexObj.property
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.obj (reindexObj p f x).1 = V := sorry
/- Proof strategy: use the second projection of the standard fiber object `reindexObj p f x`. -/

/-- The intrinsic reindexing arrow is strongly cartesian over the displayed base morphism. -/
instance cartesianHom.isStronglyCartesian
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.IsStronglyCartesian f (cartesianHom p f x) := sorry
/- Proof strategy: normalize the endpoint equality stored by `x`, then apply
`lift.isStronglyCartesian` to the same selected lift that defines `cartesianHom`. -/

/-- The intrinsic reindexing arrow lies over the displayed base morphism. -/
theorem cartesianHom.isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.IsHomLift f (cartesianHom p f x) := sorry
/- Proof strategy: use the `IsHomLift` instance inherited from
`cartesianHom.isStronglyCartesian`. -/

/-- The projection of the intrinsic cartesian arrow is the displayed base morphism, up to the
endpoint transports stored by the two standard-fiber objects. -/
@[simp]
theorem cartesianHom.map
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U) :
    p.map (cartesianHom p f x) =
      eqToHom (reindexObj p f x).2 ≫ f ≫ eqToHom x.2.symm := sorry
/- Proof strategy: apply `IsHomLift.fac'` to `cartesianHom.isHomLift p f x`. -/

/-- The domain of any lift over `f` with codomain `x` is the intrinsic reindexing object. -/
theorem reindexObj.eq_of_isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U)
    {a : S} (φ : a ⟶ x.1) (hφ : p.IsHomLift f φ) :
    (reindexObj p f x).1 = a := sorry
/- Proof strategy: transport `hφ` across the endpoint equality of `x`, package it as a
`Functor.HomLift`, and compare it with `lift p (f ≫ eqToHom x.2.symm)` using `lift.eq`. -/

/-- Every lift over `f` with codomain `x` is the intrinsic cartesian arrow, after transporting
its domain along uniqueness. -/
theorem cartesianHom.eq_of_isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : C} (f : V ⟶ U) (x : p.Fiber U)
    {a : S} (φ : a ⟶ x.1) (hφ : p.IsHomLift f φ) :
    cartesianHom p f x =
      eqToHom (reindexObj.eq_of_isHomLift p f x φ hφ) ≫ φ := sorry
/- Proof strategy: use equality of the two complete `Functor.HomLift` packages and eliminate the
resulting equality of their domain objects. -/

/-- Intrinsic reindexing along an identity fixes the fiber object. -/
@[simp]
theorem reindexObj.id
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    (U : C) (x : p.Fiber U) :
    reindexObj p (𝟙 U) x = x := sorry
/- Proof strategy: compare the selected lift of the identity with the identity of `x.1`; strict
discreteness of the standard fiber also identifies the attached membership witnesses. -/

/-- The intrinsic cartesian arrow over an identity is the identity after transporting its source
along `reindexObj.id`. -/
@[simp]
theorem cartesianHom.id
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    (U : C) (x : p.Fiber U) :
    cartesianHom p (𝟙 U) x =
      eqToHom (congrArg (fun y : p.Fiber U => y.1) (reindexObj.id p U x)) := sorry
/- Proof strategy: the identity of `x.1` is a lift over `𝟙 U`; apply
`cartesianHom.eq_of_isHomLift` and identify its source using `reindexObj.id`. -/

/-- Intrinsic reindexing along a composite is iterated intrinsic reindexing. -/
@[simp]
theorem reindexObj.comp
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    reindexObj p (g ≫ f) x =
      reindexObj p g (reindexObj p f x) := sorry
/- Proof strategy: the composite of the two selected cartesian arrows is a lift of `g ≫ f`;
compare its complete lift package with the selected composite lift using `lift.eq`. -/

/-- The intrinsic cartesian arrow over a composite is the composite of the intrinsic cartesian
arrows, after transporting its source along `reindexObj.comp`. -/
@[simp]
theorem cartesianHom.comp
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    cartesianHom p (g ≫ f) x =
      eqToHom
          (congrArg (fun y : p.Fiber W => y.1) (reindexObj.comp p f g x)) ≫
        cartesianHom p g (reindexObj p f x) ≫ cartesianHom p f x := sorry
/- Proof strategy: the displayed composite is a lift of `g ≫ f`; apply
`cartesianHom.eq_of_isHomLift` and normalize its source with `reindexObj.comp`. -/

end CategoryTheory.Functor.IsDiscreteFibration
