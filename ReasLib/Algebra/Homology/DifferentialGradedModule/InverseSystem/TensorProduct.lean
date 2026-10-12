/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.Localization
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Restriction
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative derived tensor towers over inverse systems of DGAs

Fixing a left DG-module system `N` over `A`, ordinary relative tensor and its restriction
comparison produce a sequential inverse system in `D(R)` from every right DG-module system.
The total left-derived functor of this construction is the canonical tensor-tower functor out of
the global localization `D(ℕ, A)`.
-/

@[expose] public section

noncomputable section

universe u x v w

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.TensorProduct.FixedLeft

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- The adjacent transition in the localized relative tensor tower of two ordinary module
systems. -/
def step (M : System.{u, x, v} A) (N : LeftSystem.{u, x, w} A) (n : ℕ) :
    DerivedCategory.Q.obj
        (DifferentialGradedModule.TensorProduct.complex (M.obj (n + 1))
          (LeftDifferentialGradedModule.unop (N.obj (n + 1)))) ⟶
      DerivedCategory.Q.obj
        (DifferentialGradedModule.TensorProduct.complex (M.obj n)
          (LeftDifferentialGradedModule.unop (N.obj n))) :=
  DerivedCategory.Q.map
    (DifferentialGradedModule.TensorProduct.mapRight
          (LeftDifferentialGradedModule.unop (N.obj (n + 1))) (M.map n) ≫
      DifferentialGradedModule.TensorProduct.mapLeft
          ((A.stepMap n).restrictModule (M.obj n))
          ((LeftDifferentialGradedModule.unopFunctor (A.obj (op (n + 1)))).map
            (N.map n)) ≫
      DifferentialGradedModule.TensorProduct.restrictMap
        (A.stepMap n) (M.obj n) (N.obj n))

/-- The relative tensor tower associated to two ordinary DG-module systems. -/
@[stacks 0GZI "relative tensor tower over an inverse system of DGAs"]
def tower (M : System.{u, x, v} A) (N : LeftSystem.{u, x, w} A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) :=
  Functor.ofOpSequence
    (X := fun n ↦ DerivedCategory.Q.obj
      (DifferentialGradedModule.TensorProduct.complex (M.obj n)
        (LeftDifferentialGradedModule.unop (N.obj n))))
    (step M N)

/-- Stage `n` of the ordinary relative tensor tower is localization of the explicit stagewise
relative tensor complex. -/
@[simp]
theorem tower_obj (M : System.{u, x, v} A) (N : LeftSystem.{u, x, w} A)
    (n : ℕ) :
    (tower M N).obj (op n) = DerivedCategory.Q.obj
      (DifferentialGradedModule.TensorProduct.complex (M.obj n)
        (LeftDifferentialGradedModule.unop (N.obj n))) := sorry

/-- A morphism of right module systems acts stagewise on fixed-left relative tensor towers. -/
def towerMapApp (N : LeftSystem.{u, x, w} A)
    {M M' : System.{u, x, v} A} (f : M ⟶ M') (n : ℕ) :
    (tower M N).obj (op n) ⟶ (tower M' N).obj (op n) :=
  DerivedCategory.Q.map
    (DifferentialGradedModule.TensorProduct.mapRight
      (LeftDifferentialGradedModule.unop (N.obj n)) (f.app n))

/-- Stagewise tensor maps of a right-system morphism assemble into a map of inverse systems. -/
def towerMap (N : LeftSystem.{u, x, w} A)
    {M M' : System.{u, x, v} A} (f : M ⟶ M') :
    tower M N ⟶ tower M' N :=
  NatTrans.ofOpSequence (towerMapApp N f) (fun _ ↦ sorry)

/-- Fixed-left relative tensor towers form a functor on ordinary right DG-module systems. -/
def source (N : LeftSystem.{u, x, w} A) :
    System.{u, x, v} A ⥤
      SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) where
  obj M := tower M N
  map f := towerMap N f
  map_id := sorry
  map_comp := sorry

/-- Property-(P) resolutions of module systems make the fixed-left tensor-tower source defined
at every object of the global localization. -/
@[stacks 0GZI "existence of relative derived tensor towers"]
instance sourceEverywhereDefined (N : LeftSystem.{u, x, w} A) :
    Functor.LeftDerived.EverywhereDefined (source.{u, x, v, w} N)
      (DifferentialGradedModule.InverseSystem.quasiIso A) := sorry

/-- The fixed-left tensor-tower source admits a canonical total left-derived functor. -/
instance sourceHasLeftDerivedFunctor (N : LeftSystem.{u, x, w} A) :
    (source.{u, x, v, w} N).HasLeftDerivedFunctor
      (DifferentialGradedModule.InverseSystem.quasiIso A) := sorry

/-- The relative derived tensor-tower functor from the global category `D(ℕ, A)`. -/
@[stacks 0GZI "relative derived tensor tower functor"]
noncomputable def functor (N : LeftSystem.{u, x, w} A) :
    DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A ⥤
      SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) :=
  (source N).totalLeftDerived
    (DifferentialGradedModule.InverseSystem.Derived.Q A)
    (DifferentialGradedModule.InverseSystem.quasiIso A)

/-- The canonical comparison from the global relative derived tensor-tower functor to its
ordinary source before localization. -/
noncomputable def counit (N : LeftSystem.{u, x, w} A) :
    DifferentialGradedModule.InverseSystem.Derived.Q A ⋙ functor N ⟶ source N :=
  (source N).totalLeftDerivedCounit
    (DifferentialGradedModule.InverseSystem.Derived.Q A)
    (DifferentialGradedModule.InverseSystem.quasiIso A)

/-- The selected fixed-left tensor-tower functor and comparison satisfy the universal
property of the total left-derived functor. -/
noncomputable instance functorIsLeftDerived (N : LeftSystem.{u, x, w} A) :
    (functor N).IsLeftDerivedFunctor (counit N)
      (DifferentialGradedModule.InverseSystem.quasiIso A) := sorry

/-- A morphism of left module systems acts stagewise on relative tensor towers. -/
def leftTowerMapApp {N N' : LeftSystem.{u, x, w} A} (g : N ⟶ N')
    (M : System.{u, x, v} A) (n : ℕ) :
    (tower M N).obj (op n) ⟶ (tower M N').obj (op n) :=
  DerivedCategory.Q.map
    (DifferentialGradedModule.TensorProduct.mapLeft (M.obj n)
      ((LeftDifferentialGradedModule.unopFunctor (A.obj (op n))).map (g.app n)))

/-- Stagewise maps induced by a left-system morphism assemble into a map of relative tensor
towers. -/
def leftTowerMap {N N' : LeftSystem.{u, x, w} A} (g : N ⟶ N')
    (M : System.{u, x, v} A) : tower M N ⟶ tower M N' :=
  NatTrans.ofOpSequence (leftTowerMapApp g M) (fun _ ↦ sorry)

/-- A morphism of left module systems induces a natural transformation between the ordinary
fixed-left tensor-tower sources. -/
def sourceMap {N N' : LeftSystem.{u, x, w} A} (g : N ⟶ N') :
    source.{u, x, v, w} N ⟶ source N' where
  app M := leftTowerMap g M
  naturality := sorry

/-- A morphism of left module systems induces the canonical transformation between relative
derived tensor-tower functors. -/
noncomputable def map {N N' : LeftSystem.{u, x, w} A} (g : N ⟶ N') :
    functor.{u, x, v, w} N ⟶ functor N' :=
  Functor.leftDerivedNatTrans (functor N) (functor N')
    (counit N) (counit N') (DifferentialGradedModule.InverseSystem.quasiIso A)
    (sourceMap g)

/-- The tensor-tower transformation induced by an identity left-system map is the identity. -/
@[simp]
theorem map_id (N : LeftSystem.{u, x, w} A) :
    map (𝟙 N) = 𝟙 (functor.{u, x, v, w} N) := sorry

/-- Tensor-tower transformations preserve composition of left-system maps. -/
@[simp]
theorem map_comp {L M N : LeftSystem.{u, x, w} A}
    (f : L ⟶ M) (g : M ⟶ N) :
    map (f ≫ g) = map f ≫ map g := sorry

end DifferentialGradedModule.InverseSystem.TensorProduct.FixedLeft
