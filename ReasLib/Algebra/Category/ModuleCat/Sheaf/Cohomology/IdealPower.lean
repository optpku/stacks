module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.CategoryTheory.InverseSystem.Positive.Sequential
public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower.Multiplication
public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical ideal-power actions on cohomology of module sheaves

The presented ideal-power terms and their multiplication diagrams live in the generic positive
inverse-system layer.  This leaf only identifies the associated-graded action on their exact-degree
site cohomology with the maps induced by those diagrams.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.PNatInverseSystem.IdealPower

noncomputable section

universe u v w

namespace CategoryTheory.SiteModuleCohomology.IdealPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]

section Cohomology

variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- The installed associated-graded action is canonical when multiplication by every homogeneous
stage representative agrees with the cohomology map induced by the corresponding ideal-power
term map.  Since every homogeneous class has a stage representative, this determines the action
on all homogeneous scalars. -/
@[stacks 0GYM "canonical graded action on ideal-power cohomology"]
def IsCanonicalAction
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : Presentation I F) (μ : Multiplication P) (p : ℕ)
    (module : Module (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p)) : Prop :=
  ∀ (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
      (x : SiteModuleCohomology.piece (terms P) p n),
    module.toSMul.smul
      ((Ideal.AssociatedGraded.stageClassLinear I d a :
        Ideal.AssociatedGraded.grade I d) : Ideal.AssociatedGraded.ring I)
        (DirectSum.of (SiteModuleCohomology.piece (terms P) p) n x) =
      DirectSum.of (SiteModuleCohomology.piece (terms P) p) (d + n)
        (((siteModuleCohomologyFunctor p).map (μ.termMap d n a)).hom x)

/-- The defining computation rule for a canonical action on a homogeneous stage
representative. -/
theorem IsCanonicalAction.smul_of
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : Presentation I F} {μ : Multiplication P} {p : ℕ}
    (module : Module (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p))
    (h : IsCanonicalAction P μ p module) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d)
    (x : SiteModuleCohomology.piece (terms P) p n) :
    module.toSMul.smul
      ((Ideal.AssociatedGraded.stageClassLinear I d a :
        Ideal.AssociatedGraded.grade I d) : Ideal.AssociatedGraded.ring I)
        (DirectSum.of (SiteModuleCohomology.piece (terms P) p) n x) =
      DirectSum.of (SiteModuleCohomology.piece (terms P) p) (d + n)
        (((siteModuleCohomologyFunctor p).map (μ.termMap d n a)).hom x) := sorry

/-- A canonical action carries homogeneous cohomology classes to the sum of their degrees. -/
theorem IsCanonicalAction.smul_mem
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : Presentation I F} {μ : Multiplication P} {p : ℕ}
    (module : Module (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p))
    (h : IsCanonicalAction P μ p module) ⦃d n : ℕ⦄
    {a : Ideal.AssociatedGraded.ring I}
    {x : SiteModuleCohomology.directSum (terms P) p} :
    a ∈ Ideal.AssociatedGraded.grade I d →
      x ∈ SiteModuleCohomology.grade (terms P) p n →
        module.toSMul.smul a x ∈
          SiteModuleCohomology.grade (terms P) p (d +ᵥ n) := sorry

/-- The canonical graded-module structure on exact-degree ideal-power cohomology.

The class owns the module action and its identification with the maps induced by the ideal-power
multiplication diagrams.  Homogeneous closure is derived from this computation. -/
@[stacks 0GYM "canonical graded module on ideal-power cohomology"]
class Action
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : Presentation I F) (p : ℕ) where
  /-- The multiplication diagrams inducing the action. -/
  mul : Multiplication P
  /-- The associated-graded module structure. -/
  module : Module (Ideal.AssociatedGraded.ring I)
    (SiteModuleCohomology.directSum (terms P) p)
  /-- The module action is induced by the presented multiplication diagrams. -/
  isCanonical : IsCanonicalAction P mul p module

/-- A canonical action supplies the associated-graded module instance. -/
instance Action.instModule
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : Presentation I F} {p : ℕ}
    [action : Action P p] :
    Module (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p) :=
  action.module

/-- The installed canonical action preserves the homogeneous grading. -/
theorem Action.smul_mem
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : Presentation I F} {p : ℕ} [Action P p]
    ⦃d n : ℕ⦄ {a : Ideal.AssociatedGraded.ring I}
    {x : SiteModuleCohomology.directSum (terms P) p} :
    a ∈ Ideal.AssociatedGraded.grade I d →
      x ∈ SiteModuleCohomology.grade (terms P) p n →
        a • x ∈ SiteModuleCohomology.grade (terms P) p (d +ᵥ n) := sorry

/-- A canonical action supplies the homogeneous-action instance. -/
instance Action.instGradedSMul
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : Presentation I F} {p : ℕ}
    [action : Action P p] :
    SetLike.GradedSMul (Ideal.AssociatedGraded.grade I)
      (SiteModuleCohomology.grade (terms P) p) where
  smul_mem := Action.smul_mem (P := P) (p := p)

/-- Multiplication by a homogeneous representative computes through its ideal-power term map. -/
theorem Action.smul_of
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : Presentation I F} {p : ℕ}
    [Action P p] (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d)
    (x : SiteModuleCohomology.piece (terms P) p n) :
    ((Ideal.AssociatedGraded.stageClassLinear I d a :
        Ideal.AssociatedGraded.grade I d) : Ideal.AssociatedGraded.ring I) •
        DirectSum.of (SiteModuleCohomology.piece (terms P) p) n x =
      DirectSum.of (SiteModuleCohomology.piece (terms P) p) (d + n)
        (((siteModuleCohomologyFunctor p).map
          ((Action.mul (P := P) (p := p)).termMap d n a)).hom x) := sorry

end Cohomology

end CategoryTheory.SiteModuleCohomology.IdealPower
