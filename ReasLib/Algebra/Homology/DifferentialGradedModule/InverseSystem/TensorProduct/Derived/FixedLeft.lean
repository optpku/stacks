/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.TensorProduct.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed represented left factors in relative derived tensor towers

The stagewise relative derived tensor tower with an ordinary left-system representative is
functorial in the global right derived system.  Its explicit comparison to the ordinary tensor
source makes it another left-derived model of the existing fixed-left source; uniqueness of left
derived functors then identifies the two canonical tower constructions.
-/

@[expose] public section

noncomputable section

universe u x v w

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.TensorProduct.Derived.RepresentedLeft

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- The stagewise action of a right global derived morphism with an ordinary left-system
representative fixed. -/
noncomputable def mapRightApp (N : LeftSystem.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') (n : ℕ) :
    (tower M N).obj (op n) ⟶ (tower M' N).obj (op n) :=
  ((DifferentialGradedModule.TensorProduct.Derived.functor (A.obj (op n))).map
    ((DifferentialGradedModule.InverseSystem.Derived.eval A n).map f)).app
      ((DifferentialGradedModule.InverseSystem.Derived.Left.stageSource A n).obj N)

/-- Stagewise right-factor maps commute with adjacent represented tensor-tower transitions. -/
theorem mapRightApp_naturality (N : LeftSystem.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') (n : ℕ) :
    (tower M N).stepMap n ≫ mapRightApp N f n =
      mapRightApp N f (n + 1) ≫ (tower M' N).stepMap n := sorry

/-- A right global derived morphism induces a morphism of represented tensor towers. -/
noncomputable def mapRight (N : LeftSystem.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') : tower M N ⟶ tower M' N :=
  NatTrans.ofOpSequence (mapRightApp N f) (mapRightApp_naturality N f)

/-- The component of a represented right-factor tower map is its stagewise tensor map. -/
@[simp]
theorem mapRight_app (N : LeftSystem.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') (n : ℕ) :
    (mapRight N f).app (op n) = mapRightApp N f n := sorry

/-- Represented right-factor tower maps preserve identities. -/
@[simp]
theorem mapRight_id
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : LeftSystem.{u, x, w} A) :
    mapRight N (𝟙 M) = 𝟙 (tower M N) := sorry

/-- Represented right-factor tower maps preserve composition. -/
@[simp]
theorem mapRight_comp (N : LeftSystem.{u, x, w} A)
    {L M P : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : L ⟶ M) (g : M ⟶ P) :
    mapRight N (f ≫ g) = mapRight N f ≫ mapRight N g := sorry

/-- The represented relative derived tensor-tower functor for a fixed ordinary left module
system. -/
@[stacks 0GZI "represented fixed-left relative derived tensor-tower functor"]
noncomputable def functor (N : LeftSystem.{u, x, w} A) :
    DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A ⥤
      SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) where
  obj M := tower M N
  map f := mapRight N f
  map_id := sorry
  map_comp := sorry

/-- Evaluating the represented fixed-left functor gives its stagewise tensor tower. -/
@[simp]
theorem functor_obj (N : LeftSystem.{u, x, w} A)
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A) :
    (functor N).obj M = tower M N := sorry

/-- The stage component of the comparison from represented relative derived tensor to the
ordinary fixed-left tensor source. -/
@[stacks 0GZI "counit stage for represented relative derived tensor towers"]
noncomputable def counitStage (N : LeftSystem.{u, x, w} A)
    (M : System.{u, x, v} A) (n : ℕ) :
    (tower ((DifferentialGradedModule.InverseSystem.Derived.Q A).obj M) N).obj (op n) ⟶
      (TensorProduct.FixedLeft.tower M N).obj (op n) :=
  ((DifferentialGradedModule.TensorProduct.Derived.functor (A.obj (op n))).map
      ((DifferentialGradedModule.InverseSystem.Derived.evalFactors A n).hom.app M)).app
        ((DifferentialGradedModule.InverseSystem.Derived.Left.stageSource A n).obj N) ≫
    (DifferentialGradedModule.TensorProduct.Derived.factorizationIso (A.obj (op n))
      ((DifferentialGradedModule.InverseSystem.Derived.stageSource A n).obj M)
      ((DifferentialGradedModule.toK (A.obj (op n)).opposite).obj (N.obj n))).hom ≫
    (DifferentialGradedModule.TensorProduct.Derived.FixedLeft.counit (N.obj n)).app
      ((DifferentialGradedModule.toK (A.obj (op n))).obj (M.obj n))

/-- The represented counit stages commute with adjacent tensor-tower transitions. -/
theorem counitStage_naturality (N : LeftSystem.{u, x, w} A)
    (M : System.{u, x, v} A) (n : ℕ) :
    (tower ((DifferentialGradedModule.InverseSystem.Derived.Q A).obj M) N).stepMap n ≫
        counitStage N M n =
      counitStage N M (n + 1) ≫ (TensorProduct.FixedLeft.tower M N).stepMap n := sorry

/-- The comparison from a represented tensor tower to the ordinary fixed-left source at one
ordinary right module system. -/
noncomputable def counitApp (N : LeftSystem.{u, x, w} A)
    (M : System.{u, x, v} A) :
    (functor N).obj ((DifferentialGradedModule.InverseSystem.Derived.Q A).obj M) ⟶
      (TensorProduct.FixedLeft.source N).obj M :=
  NatTrans.ofOpSequence (counitStage N M) (counitStage_naturality N M)

/-- The represented counit is natural in the ordinary right module system. -/
theorem counit_naturality (N : LeftSystem.{u, x, w} A)
    {M M' : System.{u, x, v} A} (f : M ⟶ M') :
    ((DifferentialGradedModule.InverseSystem.Derived.Q A ⋙ functor N).map f) ≫
        counitApp N M' =
      counitApp N M ≫ (TensorProduct.FixedLeft.source N).map f := sorry

/-- The canonical comparison from the represented fixed-left tensor-tower functor to its
ordinary source. -/
@[stacks 0GZI "counit of the represented fixed-left tensor-tower functor"]
noncomputable def counit (N : LeftSystem.{u, x, w} A) :
    DifferentialGradedModule.InverseSystem.Derived.Q A ⋙ functor N ⟶
      TensorProduct.FixedLeft.source N where
  app M := counitApp N M
  naturality := fun {M M'} f ↦
    counit_naturality N (M := M) (M' := M') f

/-- The represented fixed-left tower functor satisfies the universal property of the total
left-derived functor. -/
@[stacks 0GZI "left-derived property of represented relative tensor towers"]
noncomputable instance functorIsLeftDerived (N : LeftSystem.{u, x, w} A) :
    (functor N).IsLeftDerivedFunctor (counit N)
      (DifferentialGradedModule.InverseSystem.quasiIso A) := sorry

/-- The represented stagewise model and the existing total left-derived fixed-left model are
canonically naturally isomorphic. -/
@[stacks 0GZI "comparison of canonical fixed-left relative derived tensor towers"]
noncomputable def fixedLeftIso (N : LeftSystem.{u, x, w} A) :
    functor.{u, x, v, w} N ≅ TensorProduct.FixedLeft.functor N :=
  (TensorProduct.FixedLeft.functor N).leftDerivedUnique
    (functor N) (counit N) (TensorProduct.FixedLeft.counit N)
    (DifferentialGradedModule.InverseSystem.quasiIso A)

/-- The canonical fixed-left comparison is compatible with the two left-derived counits. -/
theorem fixedLeftIso_counit (N : LeftSystem.{u, x, w} A) :
    Functor.whiskerLeft (DifferentialGradedModule.InverseSystem.Derived.Q A)
          (fixedLeftIso.{u, x, v, w} N).hom ≫
        TensorProduct.FixedLeft.counit N =
      counit N := sorry

/-- Objectwise comparison between the represented stagewise tensor tower and the existing
fixed-left total left-derived tower. -/
noncomputable abbrev fixedLeftIsoApp (N : LeftSystem.{u, x, w} A)
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A) :
    tower M N ≅ (TensorProduct.FixedLeft.functor N).obj M :=
  (fixedLeftIso N).app M

end DifferentialGradedModule.InverseSystem.TensorProduct.Derived.RepresentedLeft
