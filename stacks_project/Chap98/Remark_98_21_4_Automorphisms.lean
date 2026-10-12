/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Remark_98_21_4_Automorphisms_InfHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Automorphisms of lifts along a first-order thickening

In the setting of Lemma 98.21.2, infinitesimal automorphisms of two lifts of `x`
to a square-zero thickening `A' ⟶ A` act on the Hom-set in `Lift(x, A')`. After
identifying both groups with `Inf_x(I)` via `infIso`, the actions agree and yield
a simply transitive `Inf_x(I)`-action as soon as Hom is nonempty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
variable {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}

/-- Remark 98.21.4 (Automorphisms) (1): in the setting of Lemma 98.21.2, lifts
`x'`, `x''` of `x` to `A'` admit the composition map
`Inf(x'/x) × Mor_Lift(x, A')(x', x'') × Inf(x''/x) ⟶ Mor_Lift(x, A')(x', x'')`
whose underlying fibre morphism is `α.val.hom ≫ φ.val ≫ β.val.hom`. -/
@[stacks 07YB]
theorem infHomComp_apply [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    (α : infinitesimalAut x') (φ : x' ⟶ x'') (β : infinitesimalAut x'') :
    (infHomComp x' x'' α φ β).val = α.val.hom ≫ φ.val ≫ β.val.hom := sorry

/-- Remark 98.21.4 (Automorphisms) (2): if `Mor_Lift(x, A')(x', x'')` is nonempty,
then the left action of `Inf(x'/x)` on that Hom-set is simply transitive. -/
@[stacks 07YB]
theorem infHomLeftAct_simplyTransitive [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x'') :
    ∃! α : infinitesimalAut x', infHomLeftAct x' x'' α φ = ψ := sorry

/-- Remark 98.21.4 (Automorphisms) (3): if `Mor_Lift(x, A')(x', x'')` is nonempty,
then the right action of `Inf(x''/x)` on that Hom-set is simply transitive. -/
@[stacks 07YB]
theorem infHomRightAct_simplyTransitive [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x'') :
    ∃! β : infinitesimalAut x'', infHomRightAct x' x'' φ β = ψ := sorry

/-- Remark 98.21.4 (Automorphisms) (4): the left `Inf(x'/x)`-action and the right
`Inf(x''/x)`-action agree after identifying both groups with `Inf_x(I)` via
`infIso`. -/
@[stacks 07YB]
theorem infHom_left_eq_right [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    (t : (infFunctor x).obj (kernelObj fA)) (φ : x' ⟶ x'') :
    infHomLeftAct x' x'' ((infIso x x').hom t) φ =
      infHomRightAct x' x'' φ ((infIso x x'').hom t) := sorry

/-- Remark 98.21.4 (Automorphisms) (5): the resulting action of `Inf_x(I)` on
`Mor_Lift(x, A')(x', x'')` is simply transitive as soon as that Hom-set is
nonempty. -/
@[stacks 07YB]
theorem infHomAct_simplyTransitive [HasStrongRimSchlessinger X]
    [RingHom.IsSquareZeroExtension fA.hom]
    (x : X.p.Fiber (Over.mk σA)) (x' x'' : liftCat x fA hfA)
    [Nonempty (x' ⟶ x'')] (φ ψ : x' ⟶ x'') :
    ∃! t : (infFunctor x).obj (kernelObj fA), infHomAct x x' x'' t φ = ψ := sorry

end AlgebraicGeometry.GroupoidsOver
