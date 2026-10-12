/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_21_2_Functor

/-!
# Infinitesimal actions on morphisms of lifts

For lifts `x'`, `x''` of a fibre object `x` along `A' ⟶ A`, infinitesimal
automorphisms of the two lifts act on `x' ⟶ x''` by fibre composition. After
identifying both infinitesimal automorphism groups with `Inf_x(I)` via `infIso`,
this yields a well-defined action of `Inf_x(I)` on Hom.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
variable {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}

/-- The composition map
`Inf(x'/x) × Mor_Lift(x, A')(x', x'') × Inf(x''/x) ⟶ Mor_Lift(x, A')(x', x'')`,
sending `(α, φ, β)` to the lift morphism whose underlying fibre arrow is
`α.val.hom ≫ φ.val ≫ β.val.hom`. -/
def infHomComp {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (α : infinitesimalAut x') (φ : x' ⟶ x'') (β : infinitesimalAut x'') :
    x' ⟶ x'' :=
  UnderLift.homMk (α.val.hom ≫ φ.val ≫ β.val.hom) sorry

/-- The underlying fibre morphism of `infHomComp` is the composite
`α.val.hom ≫ φ.val ≫ β.val.hom`. -/
theorem infHomComp_val {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (α : infinitesimalAut x') (φ : x' ⟶ x'') (β : infinitesimalAut x'') :
    (infHomComp x' x'' α φ β).val = α.val.hom ≫ φ.val ≫ β.val.hom := sorry

/-- Composition against identity infinitesimal automorphisms recovers `φ`. -/
theorem infHomComp_one {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (φ : x' ⟶ x'') :
    infHomComp x' x'' 1 φ 1 = φ := sorry

/-- The left action of `Inf(x'/x)` on `Mor_Lift(x, A')(x', x'')`. -/
def infHomLeftAct {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (α : infinitesimalAut x') (φ : x' ⟶ x'') : x' ⟶ x'' :=
  infHomComp x' x'' α φ 1

/-- The right action of `Inf(x''/x)` on `Mor_Lift(x, A')(x', x'')`. -/
def infHomRightAct {x : X.p.Fiber (Over.mk σA)} (x' x'' : liftCat x fA hfA)
    (φ : x' ⟶ x'') (β : infinitesimalAut x'') : x' ⟶ x'' :=
  infHomComp x' x'' 1 φ β

/-- The identity of `Inf(x'/x)` acts trivially on the left. -/
theorem infHomLeftAct_one {x : X.p.Fiber (Over.mk σA)}
    (x' x'' : liftCat x fA hfA) (φ : x' ⟶ x'') :
    infHomLeftAct x' x'' 1 φ = φ := sorry

/-- The identity of `Inf(x''/x)` acts trivially on the right. -/
theorem infHomRightAct_one {x : X.p.Fiber (Over.mk σA)}
    (x' x'' : liftCat x fA hfA) (φ : x' ⟶ x'') :
    infHomRightAct x' x'' φ 1 = φ := sorry

variable [HasStrongRimSchlessinger X]
variable [RingHom.IsSquareZeroExtension fA.hom]

/-- The action of `Inf_x(I)` on `Mor_Lift(x, A')(x', x'')` obtained by transporting
the left `Inf(x'/x)`-action along `infIso`. -/
def infHomAct (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    (t : (infFunctor x).obj (kernelObj fA)) (φ : x' ⟶ x'') : x' ⟶ x'' :=
  infHomLeftAct x' x'' ((infIso x x').hom t) φ

/-- `infHomAct` is the left `Inf(x'/x)`-action transported along `infIso`. -/
theorem infHomAct_eq_left (x : X.p.Fiber (Over.mk σA))
    (x' x'' : liftCat x fA hfA) (t : (infFunctor x).obj (kernelObj fA))
    (φ : x' ⟶ x'') :
    infHomAct x x' x'' t φ =
      infHomLeftAct x' x'' ((infIso x x').hom t) φ := sorry

/-- `infHomAct` agrees with the right `Inf(x''/x)`-action transported along
`infIso`. -/
theorem infHomAct_eq_right (x : X.p.Fiber (Over.mk σA))
    (x' x'' : liftCat x fA hfA) (t : (infFunctor x).obj (kernelObj fA))
    (φ : x' ⟶ x'') :
    infHomAct x x' x'' t φ =
      infHomRightAct x' x'' φ ((infIso x x'').hom t) := sorry

/-- The zero element of `Inf_x(I)` acts trivially. -/
theorem infHomAct_zero (x : X.p.Fiber (Over.mk σA))
    (x' x'' : liftCat x fA hfA) (φ : x' ⟶ x'') :
    infHomAct x x' x'' (0 : (infFunctor x).obj (kernelObj fA)) φ = φ := sorry

end AlgebraicGeometry.GroupoidsOver
