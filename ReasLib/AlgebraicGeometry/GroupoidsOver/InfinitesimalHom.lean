module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation

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
    (infHomComp x' x'' α φ β).val = α.val.hom ≫ φ.val ≫ β.val.hom := rfl

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

/-- Multiplication of source infinitesimal automorphisms gives successive left
operations on morphisms of lifts across a square-zero extension. -/
theorem infHomLeftAct_mul [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom] {x : X.p.Fiber (Over.mk σA)}
    (x' x'' : liftCat x fA hfA) (α β : infinitesimalAut x') (φ : x' ⟶ x'') :
    infHomLeftAct x' x'' (α * β) φ =
      infHomLeftAct x' x'' α (infHomLeftAct x' x'' β φ) := sorry

/-- Multiplication of target infinitesimal automorphisms gives successive right
operations on morphisms of lifts across a square-zero extension. -/
theorem infHomRightAct_mul [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom] {x : X.p.Fiber (Over.mk σA)}
    (x' x'' : liftCat x fA hfA) (φ : x' ⟶ x'') (α β : infinitesimalAut x'') :
    infHomRightAct x' x'' φ (α * β) =
      infHomRightAct x' x'' (infHomRightAct x' x'' φ α) β := sorry

/-- The action of `Inf_x(I)` on `Mor_Lift(x, A')(x', x'')` obtained by transporting
the left `Inf(x'/x)`-action along `infIso`. -/
def infHomAct [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    (t : (infFunctor x).obj (kernelObj fA)) (φ : x' ⟶ x'') : x' ⟶ x'' :=
  infHomLeftAct x' x'' ((infIso x x').hom t) φ

/-- `infHomAct` is the left `Inf(x'/x)`-action transported along `infIso`. -/
theorem infHomAct_eq_left [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA))
    (x' x'' : liftCat x fA hfA) (t : (infFunctor x).obj (kernelObj fA))
    (φ : x' ⟶ x'') :
    infHomAct x x' x'' t φ =
      infHomLeftAct x' x'' ((infIso x x').hom t) φ := rfl

/-- The zero element of `Inf_x(I)` acts trivially. -/
theorem infHomAct_zero [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA))
    (x' x'' : liftCat x fA hfA) (φ : x' ⟶ x'') :
    infHomAct x x' x'' (0 : (infFunctor x).obj (kernelObj fA)) φ = φ := sorry

/-- Addition in the infinitesimal module corresponds to successive actions on
morphisms of lifts. -/
theorem infHomAct_add [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom] (x : X.p.Fiber (Over.mk σA))
    (x' x'' : liftCat x fA hfA) (s t : (infFunctor x).obj (kernelObj fA))
    (φ : x' ⟶ x'') :
    infHomAct x x' x'' (s + t) φ =
      infHomAct x x' x'' s (infHomAct x x' x'' t φ) := sorry

/-- Source infinitesimal automorphisms act simply transitively on each nonempty
set of morphisms between two lifts across a square-zero extension. -/
theorem infHomLeftAct_simplyTransitive [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x'') :
    ∃! α : infinitesimalAut x', infHomLeftAct x' x'' α φ = ψ := sorry

/-- Target infinitesimal automorphisms act simply transitively on each nonempty
set of morphisms between two lifts across a square-zero extension. -/
theorem infHomRightAct_simplyTransitive [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x'') :
    ∃! β : infinitesimalAut x'', infHomRightAct x' x'' φ β = ψ := sorry

/-- The source and target infinitesimal automorphism operations agree under the
canonical identifications with the infinitesimal module of the base object. -/
theorem infHom_left_eq_right [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    (t : (infFunctor x).obj (kernelObj fA)) (φ : x' ⟶ x'') :
    infHomLeftAct x' x'' ((infIso x x').hom t) φ =
      infHomRightAct x' x'' φ ((infIso x x'').hom t) := sorry

/-- The infinitesimal module of the base object acts simply transitively on each
nonempty set of morphisms between two lifts across a square-zero extension. -/
theorem infHomAct_simplyTransitive [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x'') :
    ∃! t : (infFunctor x).obj (kernelObj fA), infHomAct x x' x'' t φ = ψ := sorry

end AlgebraicGeometry.GroupoidsOver
