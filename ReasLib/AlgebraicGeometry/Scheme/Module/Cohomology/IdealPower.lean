/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Graded
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.RingTheory.ReesAlgebra.Grading.Decomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of products by ideal powers

This module constructs the degreewise cohomology of ideal-power products, the canonical
homogeneous Rees action, and the induced module structure.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace IdealPowerCohomology

/-- The degree-`n` summand of the cohomology of the product `I ^ n F`. -/
@[stacks 02O8 "ideal-power cohomology piece"]
abbrev piece {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p n : ℕ) : Type u :=
  (RingedSpace.moduleCohomology
    (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n : X.Modules) p :
      Type u)

/-- The direct sum of the degree-`p` cohomology groups of `I ^ n F` over all natural degrees. -/
@[stacks 02O8 "total ideal-power cohomology"]
abbrev carrier {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ) : Type u :=
  DirectSum ℕ fun n : ℕ ↦ piece I f F p n

/-- The homogeneous Rees action on ideal-power cohomology. -/
@[stacks 02O8 "homogeneous Rees action on ideal-power cohomology"]
noncomputable def smul
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) (x : piece I f F p n) :
    piece I f F p (m + n) :=
  (RingedSpace.moduleCohomologyMap
    (IdealPowerProduct.actionMap I f F (m := m) (n := n)
      (ReesAlgebra.Grading.coefficient I m a)) p).hom x

/-- The degree-zero unit acts trivially on ideal-power cohomology. -/
theorem one_smul
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    (x : GradedMonoid (piece I f F p)) :
    GradedMonoid.mk (0 +ᵥ x.1)
      (smul I f F p (1 : ReesAlgebra.Grading.grade I 0) x.2) = x := sorry

/-- Successive homogeneous Rees actions agree with homogeneous multiplication. -/
theorem mul_smul
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    (a b : GradedMonoid (fun d : ℕ ↦ ReesAlgebra.Grading.grade I d))
    (x : GradedMonoid (piece I f F p)) :
    GradedMonoid.mk ((a * b).1 +ᵥ x.1) (smul I f F p (a * b).2 x.2) =
      GradedMonoid.mk (a.1 +ᵥ (b.1 +ᵥ x.1))
        (smul I f F p a.2 (smul I f F p b.2 x.2)) := sorry

/-- A homogeneous Rees scalar distributes over addition in an ideal-power cohomology piece. -/
theorem smul_add
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) (x y : piece I f F p n) :
    smul I f F p a (x + y) = smul I f F p a x + smul I f F p a y := sorry

/-- Every homogeneous Rees scalar sends zero to zero in ideal-power cohomology. -/
theorem smul_zero
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) :
    smul I f F p a (0 : piece I f F p n) = 0 := sorry

/-- Addition of homogeneous Rees scalars distributes through the ideal-power cohomology action. -/
theorem add_smul
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    {m n : ℕ} (a b : ReesAlgebra.Grading.grade I m) (x : piece I f F p n) :
    smul I f F p (a + b) x = smul I f F p a x + smul I f F p b x := sorry

/-- The zero homogeneous Rees scalar acts by zero on ideal-power cohomology. -/
theorem zero_smul
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    {m n : ℕ} (x : piece I f F p n) :
    smul I f F p (0 : ReesAlgebra.Grading.grade I m) x = 0 := sorry

/-- The explicit graded Rees action on ideal-power cohomology. -/
@[reducible, stacks 02O8 "graded Rees action on ideal-power cohomology"]
noncomputable instance gmodule
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ) :
    DirectSum.Gmodule (fun n ↦ ReesAlgebra.Grading.grade I n) (piece I f F p) where
  smul := smul I f F p
  one_smul := one_smul I f F p
  mul_smul := mul_smul I f F p
  smul_add := smul_add I f F p
  smul_zero := smul_zero I f F p
  add_smul := add_smul I f F p
  zero_smul := zero_smul I f F p

/-- The canonical Rees algebra module structure on total ideal-power cohomology. -/
@[reducible, stacks 02O8 "Rees module structure on ideal-power cohomology"]
noncomputable instance module
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ) :
    Module (reesAlgebra I) (carrier I f F p) :=
  DirectSum.Gmodule.moduleFor (ReesAlgebra.Grading.grade I) (piece I f F p)
    (gmodule I f F p)

/-- The canonical Rees module action on a pure homogeneous ideal-power cohomology summand. -/
@[simp, stacks 02O8 "homogeneous Rees module action on ideal-power cohomology"]
theorem module_smul_of
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ)
    {m n : ℕ} (a : ReesAlgebra.Grading.grade I m) (x : piece I f F p n) :
    (module I f F p).toSMul.smul a (DirectSum.of (piece I f F p) n x) =
      DirectSum.of (piece I f F p) (m + n) (smul I f F p a x) := sorry

/-- For a coherent module on a proper scheme over a Noetherian affine base, the direct sum of
the cohomology of its products by ideal powers is finite over the Rees algebra. -/
@[stacks 02O8 "finite ideal-power cohomology over the Rees algebra"]
theorem finite
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent]
    (p : ℕ) :
    Module.Finite (reesAlgebra I) (carrier I f F p) := sorry

end IdealPowerCohomology

end AlgebraicGeometry.Scheme.Modules
