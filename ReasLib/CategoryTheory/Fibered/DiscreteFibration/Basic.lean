/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!
# Discrete fibrations and their canonical lifts

This file owns the intrinsic unique-lifting definition of a discrete fibration and the
choice-independent API of its selected lift.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

/-
The standard category-theoretic owner behind “fibred in sets” is a discrete fibration: every base
arrow with prescribed lifted codomain has a unique total-category lift. This formulation is more
intrinsic than storing a cleavage or a set-valued presheaf, and it does not duplicate either kind
of data. Mathlib 4.32 provides the transport-aware proposition `Functor.IsHomLift`, but not a
package for lifts with varying domains or a discrete-fibration class; `HomLift` and
`IsDiscreteFibration` supply precisely those missing layers.

Writing the exact-lift condition as `Unique (HomLift p f)` would additionally store a chosen
default lift. The separate `Nonempty` and `Subsingleton` fields state the same property without
silently choosing a cleavage.

The equivalent fibre formulation is exposed by
`IsDiscreteFibration.iff_inGroupoids_fibersDiscrete`. Its use of strict `IsDiscrete`
is essential: replacing it by `Quiver.IsThin` would produce categories fibred in setoids, the
strictly weaker and equivalence-invariant layer.
-/

/-- A lift through `p : S ⥤ C` of a base morphism `f : R ⟶ p.obj a`, including its varying
domain.

```
                  hom
       domain ─────────────▶ a
          │                  │
        p │                  │ p
          ▼                  ▼
          R ───────────────▶ p.obj a
                   f
```

The field `isHomLift` uses mathlib's transport-aware owner, so equality witnesses between the
displayed endpoints do not leak into downstream statements. -/
@[stacks 0043 "hom lift in a discrete fibration"]
structure HomLift (p : S ⥤ C) {R : C} {a : S} (f : R ⟶ p.obj a) where
  /-- The domain object of the lifted morphism. -/
  domain : S
  /-- The lifted morphism with the prescribed codomain. -/
  hom : domain ⟶ a
  /-- The total-category morphism lies over the prescribed base morphism. -/
  isHomLift : p.IsHomLift f hom

attribute [stacks 0043 "discrete-fibration lift domain field"] HomLift.domain
attribute [stacks 0043 "discrete-fibration lift morphism field"] HomLift.hom
attribute [stacks 0043 "discrete-fibration lift property field"] HomLift.isHomLift

/-- A discrete fibration has a unique lift of every
`f : R ⟶ p.obj a` with codomain `a`.

Equivalently, `p` is fibred in groupoids and every standard fiber `p.Fiber U` is strictly
discrete. The unique-lift formulation is the canonical root owner: it is independent of a chosen
cleavage and directly supports the correspondence with set-valued presheaves. -/
@[stacks 0043]
class IsDiscreteFibration (p : S ⥤ C) : Prop where
  /-- A lift exists for every base morphism with prescribed lifted codomain. -/
  homLiftNonempty {R : C} {a : S} (f : R ⟶ p.obj a) : Nonempty (HomLift p f)
  /-- Any two lifts of the same base morphism with the same codomain are equal, including their
  domain objects. -/
  homLiftSubsingleton {R : C} {a : S} (f : R ⟶ p.obj a) : Subsingleton (HomLift p f)

attribute [stacks 0043 "discrete-fibration lift existence field"]
  IsDiscreteFibration.homLiftNonempty
attribute [stacks 0043 "discrete-fibration lift uniqueness field"]
  IsDiscreteFibration.homLiftSubsingleton

namespace IsDiscreteFibration

/-- The uniquely determined lift of `f : R ⟶ p.obj a` through a discrete fibration.

This is the canonical choice boundary attached to the primitive `Nonempty` and `Subsingleton`
fields of `Functor.IsDiscreteFibration`. Its public specifications below make downstream
constructions independent of the implementation choice. -/
@[stacks 0043 "canonical lift in a discrete fibration"]
noncomputable def lift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) :
    Functor.HomLift p f :=
  Classical.choice (Functor.IsDiscreteFibration.homLiftNonempty f)

/- Axiom audit: the domain and morphism of `lift p f` are selected from the supplied
`Functor.IsDiscreteFibration p` instance. The definition depends only on `Classical.choice`; no
proof theorem or `sorryAx` supplies its non-`Prop` payload. -/

/-- The selected discrete-fibration lift lies over the displayed base morphism. -/
theorem lift.isHomLift
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) :
    p.IsHomLift f (lift p f).hom :=
  (lift p f).isHomLift

/-- Every lift of the same base morphism with the same codomain is the selected lift. -/
theorem lift.eq
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) (l : Functor.HomLift p f) :
    lift p f = l := sorry
/- Proof strategy: apply `(Functor.IsDiscreteFibration.homLiftSubsingleton f).elim`. -/

/-- The domain of the selected lift lies over the domain of the displayed base morphism. -/
@[simp]
theorem lift.domain_eq
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) :
    p.obj (lift p f).domain = R := sorry
/- Proof strategy: apply `IsHomLift.domain_eq` to `lift.isHomLift p f`. -/

/-- The image of the selected lift is the displayed base morphism, with the necessary transport
at its domain. -/
@[simp]
theorem lift.map
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) :
    p.map (lift p f).hom = eqToHom (lift.domain_eq p f) ≫ f := sorry
/- Proof strategy: use `IsHomLift.fac'`; its codomain transport is an endomorphism induced by a
proof of reflexive equality and hence is the identity. -/

end IsDiscreteFibration

namespace IsHomLift

/-- In a discrete fibration, every morphism lying over a displayed base arrow is strongly
cartesian. The factor arrow is the supplied unique lift of the remaining base arrow, transported
along the domain equality obtained from uniqueness of the composite lift. -/
theorem isStronglyCartesian
    {p : S ⥤ C} [Functor.IsDiscreteFibration p]
    {R T : C} {a b : S} {f : R ⟶ T} {φ : a ⟶ b}
    (hφ : p.IsHomLift f φ) : p.IsStronglyCartesian f φ := by
  obtain ⟨⟩ := hφ
  refine { universal_property' := ?_ }
  intro a' g φ' hφ'
  let l := IsDiscreteFibration.lift p g
  letI : p.IsHomLift g l.hom := l.isHomLift
  let composite : HomLift p (g ≫ p.map φ) :=
    ⟨l.domain, l.hom ≫ φ, IsHomLift.comp p g (p.map φ) l.hom φ⟩
  let original : HomLift p (g ≫ p.map φ) := ⟨a', φ', hφ'⟩
  have domain_eq : l.domain = a' :=
    congrArg HomLift.domain
      ((IsDiscreteFibration.homLiftSubsingleton (g ≫ p.map φ)).elim composite original)
  refine ⟨eqToHom domain_eq.symm ≫ l.hom, ⟨?_, ?_⟩, ?_⟩
  · infer_instance
  · sorry
  · sorry

end IsHomLift

namespace IsDiscreteFibration

/-- The selected lift in a discrete fibration is strongly cartesian. -/
theorem lift.isStronglyCartesian
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {R : C} {a : S} (f : R ⟶ p.obj a) :
    p.IsStronglyCartesian f (lift p f).hom :=
  IsHomLift.isStronglyCartesian (lift p f).isHomLift

end IsDiscreteFibration

end Functor

end CategoryTheory
