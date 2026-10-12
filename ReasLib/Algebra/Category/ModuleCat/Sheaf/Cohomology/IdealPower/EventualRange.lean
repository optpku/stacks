/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.CategoryTheory.InverseSystem.EventualRange
public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower.Family.Multiplication
public import ReasLib.RingTheory.Ideal.AssociatedGraded.StageClass
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stable ideal-power cohomology pieces

For a two-parameter ideal-power family, this leaf defines the exact-degree stable image

`N n = ⋂ m ≥ n, range (H^q(I ^ n F (m + 1)) ⟶ H^q(I ^ n F (n + 1)))`

as a `Submodule`, retaining the ambient `A`-module structure.  The cohomological degree `q` is an
unshifted parameter: applications at `H^(p+1)` and `H^p` are separate specializations.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.PNatInverseSystem.IdealPower

noncomputable section

universe u v w

namespace CategoryTheory.SiteModuleCohomology.IdealPower.Eventual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- The degree-`q` cohomology tower of the fixed ideal-power degree `n`. -/
@[stacks 0GYL "cohomology tower of a fixed ideal power",
  stacks 0GYN "cohomology tower of a fixed ideal power"]
abbrev cohomologyTower
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (q n : ℕ) :
    SequentialInverseSystem (ModuleCat A) :=
  siteModuleCohomologyModuleTower (P.fixedTower n) q

/-- The stable image `N_n` in exact cohomological degree `q`. -/
@[stacks 0GYL "stable ideal-power cohomology piece",
  stacks 0GYN "stable ideal-power cohomology piece"]
def piece
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (q n : ℕ) :
    Submodule A ((cohomologyTower P q n).obj (op n)) :=
  (cohomologyTower P q n).stableImage (op n)

/-- The graded direct sum of the exact-degree stable ideal-power cohomology pieces. -/
@[stacks 0GYL "direct sum of stable ideal-power cohomology",
  stacks 0GYN "direct sum of stable ideal-power cohomology"]
abbrev directSum
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (q : ℕ) :
    Type (max u v w) :=
  DirectSum ℕ (fun n ↦ piece P q n)

/-- The degree-`n` homogeneous subgroup of the stable-image direct sum. -/
@[stacks 0GYL "grading on stable ideal-power cohomology",
  stacks 0GYN "grading on stable ideal-power cohomology"]
abbrev grade
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (q n : ℕ) :
    AddSubgroup (directSum P q) :=
  AddMonoidHom.range (DirectSum.of (fun n ↦ piece P q n) n)

/-- Membership in `N_n` is membership in the range of every later cohomology transition. -/
@[stacks 0GYL "membership in a stable ideal-power cohomology piece",
  stacks 0GYN "membership in a stable ideal-power cohomology piece"]
theorem mem_piece_iff
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (q n : ℕ)
    {x : (cohomologyTower P q n).obj (op n)} :
    x ∈ piece P q n ↔
      ∀ m : ℕ, ∀ hnm : n ≤ m,
        x ∈ LinearMap.range ((cohomologyTower P q n).transitionMap hnm).hom := sorry

/-- The cohomology map induced by multiplication with one ideal-power representative at an
ambient stage. -/
abbrev cohomologyMap
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F}
    (μ : P.Multiplication) (q d n m : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    ((cohomologyTower P q n).obj (op m) : Type (max u v w)) →ₗ[A]
      ((cohomologyTower P q (d + n)).obj (op m) : Type (max u v w)) :=
  siteModuleCohomologyMapLinear q (μ.stageMap d n m a)

/-- An associated-graded action on the stable-image direct sum is canonical when every lift of a
stable class to stage `d + n`, followed by ideal-power multiplication, represents its product by
the corresponding homogeneous scalar. -/
@[stacks 0GYL "canonical action on stable ideal-power cohomology",
  stacks 0GYN "canonical action on stable ideal-power cohomology"]
def IsCanonicalAction
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F)
    (μ : P.Multiplication) (q : ℕ)
    (module : Module (Ideal.AssociatedGraded.ring I) (directSum P q)) : Prop :=
  ∀ (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
      (x : piece P q n)
      (y : (cohomologyTower P q n).obj (op (d + n))),
    ((cohomologyTower P q n).transitionMap (Nat.le_add_left n d)).hom y = x.1 →
      ∃ hmem : cohomologyMap μ q d n (d + n) a y ∈ piece P q (d + n),
        module.toSMul.smul
          ((Ideal.AssociatedGraded.stageClassLinear I d a :
            Ideal.AssociatedGraded.grade I d) : Ideal.AssociatedGraded.ring I)
            (DirectSum.of (fun n ↦ piece P q n) n x) =
          DirectSum.of (fun n ↦ piece P q n) (d + n)
            ⟨cohomologyMap μ q d n (d + n) a y, hmem⟩

/-- The defining lift-and-multiply computation for a canonical stable-image action. -/
theorem IsCanonicalAction.smul_of
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F}
    {μ : P.Multiplication} {q : ℕ}
    (module : Module (Ideal.AssociatedGraded.ring I) (directSum P q))
    (h : IsCanonicalAction P μ q module)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    (x : piece P q n)
    (y : (cohomologyTower P q n).obj (op (d + n)))
    (hy : ((cohomologyTower P q n).transitionMap
      (Nat.le_add_left n d)).hom y = x.1) :
    ∃ hmem : cohomologyMap μ q d n (d + n) a y ∈ piece P q (d + n),
      module.toSMul.smul
        ((Ideal.AssociatedGraded.stageClassLinear I d a :
          Ideal.AssociatedGraded.grade I d) : Ideal.AssociatedGraded.ring I)
          (DirectSum.of (fun n ↦ piece P q n) n x) =
        DirectSum.of (fun n ↦ piece P q n) (d + n)
          ⟨cohomologyMap μ q d n (d + n) a y, hmem⟩ := sorry

/-- A canonical stable-image action carries homogeneous classes to the sum of their degrees. -/
theorem IsCanonicalAction.smul_mem
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F}
    {μ : P.Multiplication} {q : ℕ}
    (module : Module (Ideal.AssociatedGraded.ring I) (directSum P q))
    (h : IsCanonicalAction P μ q module) ⦃d n : ℕ⦄
    {a : Ideal.AssociatedGraded.ring I} {x : directSum P q} :
    a ∈ Ideal.AssociatedGraded.grade I d →
      x ∈ grade P q n →
        module.toSMul.smul a x ∈ grade P q (d +ᵥ n) := sorry

/-- The canonical graded-module structure on exact-degree stable ideal-power cohomology.

The class owns the family multiplication, module action, and the lift-and-multiply computation
identifying the action.  Homogeneous closure is derived from this computation. -/
@[stacks 0GYL "canonical graded module on stable ideal-power cohomology",
  stacks 0GYN "canonical graded module on stable ideal-power cohomology"]
class Action
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (q : ℕ) where
  /-- The multiplication diagrams inducing the action. -/
  mul : P.Multiplication
  /-- The associated-graded module structure. -/
  module : Module (Ideal.AssociatedGraded.ring I) (directSum P q)
  /-- The module action is induced by lift-and-multiply along the family diagrams. -/
  isCanonical : IsCanonicalAction P mul q module

/-- A canonical stable-image action supplies the associated-graded module instance. -/
instance Action.instModule
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F} {q : ℕ}
    [action : Action P q] :
    Module (Ideal.AssociatedGraded.ring I) (directSum P q) :=
  action.module

/-- The installed canonical stable-image action preserves the homogeneous grading. -/
theorem Action.smul_mem
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F} {q : ℕ}
    [Action P q] ⦃d n : ℕ⦄
    {a : Ideal.AssociatedGraded.ring I} {x : directSum P q} :
    a ∈ Ideal.AssociatedGraded.grade I d →
      x ∈ grade P q n → a • x ∈ grade P q (d +ᵥ n) := sorry

/-- A canonical stable-image action supplies the homogeneous-action instance. -/
instance Action.instGradedSMul
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F} {q : ℕ}
    [action : Action P q] :
    SetLike.GradedSMul (Ideal.AssociatedGraded.grade I) (grade P q) where
  smul_mem := Action.smul_mem (P := P) (q := q)

/-- The installed stable-image action computes by lifting and multiplying. -/
theorem Action.smul_of
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    {P : PNatInverseSystem.IdealPower.Family I F} {q : ℕ}
    [Action P q]
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    (x : piece P q n)
    (y : (cohomologyTower P q n).obj (op (d + n)))
    (hy : ((cohomologyTower P q n).transitionMap
      (Nat.le_add_left n d)).hom y = x.1) :
    ∃ hmem : cohomologyMap (Action.mul (P := P) (q := q)) q d n (d + n) a y ∈
        piece P q (d + n),
      ((Ideal.AssociatedGraded.stageClassLinear I d a :
          Ideal.AssociatedGraded.grade I d) : Ideal.AssociatedGraded.ring I) •
          DirectSum.of (fun n ↦ piece P q n) n x =
        DirectSum.of (fun n ↦ piece P q n) (d + n)
          ⟨cohomologyMap (Action.mul (P := P) (q := q)) q d n (d + n) a y, hmem⟩ := sorry

end CategoryTheory.SiteModuleCohomology.IdealPower.Eventual
