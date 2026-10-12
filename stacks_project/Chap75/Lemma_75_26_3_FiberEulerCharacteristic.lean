/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.MinimalFreeModel
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

/-!
# Derived-fiber Euler characteristic on algebraic spaces

The Euler characteristic of a derived `𝒪_X`-module at a point of an algebraic space is
computed from residue-field homology of the derived étale stalk at a geometric point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The étale module-stalk functor at a geometric point preserves finite limits. -/
instance sheafModuleStalkFunctor_preservesFiniteLimits (xbar : GeometricPoint X) :
    PreservesFiniteLimits
      ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)) :=
  sorry

/-- The étale module-stalk functor at a geometric point preserves finite colimits. -/
instance sheafModuleStalkFunctor_preservesFiniteColimits (xbar : GeometricPoint X) :
    PreservesFiniteColimits
      ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)) :=
  sorry

/-- A geometric point of `X` obtained by extending a field-valued point along the algebraic
closure of its source field. -/
noncomputable def ofFieldValuedPoint (p : FieldValuedPoint X) : GeometricPoint X :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap p.K (AlgebraicClosure p.K)))
  GeometricPoint.of (AlgebraicClosure p.K) (f ≫ p.structureHom) (ofOverHomMk f rfl ≫ p.hom)

/-- A chosen geometric point of `X` lying over `x`, obtained from a field-valued
representative by algebraic closure. -/
noncomputable def geometricPointOver (x : Points X) : GeometricPoint X :=
  ofFieldValuedPoint (Quotient.out (x : Quotient (equivalentSetoid X)))

/-- The chosen geometric point over `x` has image `x`. -/
theorem geometricPointOver_image (x : Points X) :
    (geometricPointOver x).image = x := sorry

/-- The derived étale stalk of `E` at a geometric point, as an object of the derived
category of modules over the étale local ring. -/
noncomputable def stalkDerived (xbar : GeometricPoint X) (E : ModuleDerived X) :
    DerivedCategory (ModuleCat (etaleLocalRing X xbar)) :=
  ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor
    (structureSheaf X)).mapDerivedCategory.obj E

/-- Degree-`i` residue-field homology of the derived étale stalk of `E` at a geometric
point. -/
noncomputable def fiberHomology (E : ModuleDerived X) (xbar : GeometricPoint X) (i : ℤ) :
    ModuleCat (IsLocalRing.ResidueField (etaleLocalRing X xbar)) :=
  CategoryTheory.DerivedCategory.ResidueField.homology (etaleLocalRing X xbar)
    (stalkDerived xbar E) i

/-- The degree-`i` Betti number of `E` at a geometric point. -/
noncomputable def fiberBettiAt (E : ModuleDerived X) (xbar : GeometricPoint X) (i : ℤ) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField (etaleLocalRing X xbar))
    (fiberHomology E xbar i)

/-- The Euler characteristic of the derived residue-field fiber of `E` at a geometric
point. -/
noncomputable def fiberEulerCharAt (E : ModuleDerived X) (xbar : GeometricPoint X) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℤ) (fun i ↦ fiberHomology E xbar i)

/-- The degree-`i` Betti number `β_i(x)` of `E` at a point of `X`. -/
noncomputable def fiberBetti (E : ModuleDerived X) (i : ℤ) (x : Points X) : ℕ :=
  fiberBettiAt E (geometricPointOver x) i

/-- The Euler characteristic `χ_E(x)` of the derived residue-field fiber of `E` at a point
of `X`. -/
noncomputable def fiberEulerChar (E : ModuleDerived X) (x : Points X) : ℤ :=
  fiberEulerCharAt E (geometricPointOver x)

/-- The fiber Betti number is the finrank of residue-field homology at the chosen geometric
point over `x`. -/
theorem fiberBetti_apply (E : ModuleDerived X) (i : ℤ) (x : Points X) :
    fiberBetti E i x =
      Module.finrank (IsLocalRing.ResidueField (etaleLocalRing X (geometricPointOver x)))
        (fiberHomology E (geometricPointOver x) i) := sorry

/-- The derived-fiber Euler characteristic is the finsum of signed Betti numbers. -/
theorem fiberEulerChar_apply (E : ModuleDerived X) (x : Points X) :
    fiberEulerChar E x =
      ∑ᶠ i : ℤ, (Int.negOnePow i : ℤ) * fiberBetti E i x := sorry

/-- The Euler characteristic at the image of a geometric point agrees with the value at
that geometric point. -/
theorem fiberEulerChar_spec (E : ModuleDerived X) (xbar : GeometricPoint X) :
    fiberEulerChar E xbar.image = fiberEulerCharAt E xbar := sorry

/-- Isomorphic derived modules have the same derived-fiber Euler-characteristic function. -/
theorem fiberEulerChar_eq_of_iso {E F : ModuleDerived X} (e : E ≅ F) :
    fiberEulerChar E = fiberEulerChar F := sorry

/-- Perfect derived modules have finite-dimensional residue-field fiber cohomology in every
degree. -/
theorem fiberCohomology_finiteDimensional (E : ModuleDerived X) (hE : IsPerfect E)
    (xbar : GeometricPoint X) (i : ℤ) :
    FiniteDimensional (IsLocalRing.ResidueField (etaleLocalRing X xbar))
      (fiberHomology E xbar i) := sorry

/-- Perfect derived modules have residue-field fiber cohomology supported in only finitely
many degrees. -/
theorem fiberCohomology_finiteSupport (E : ModuleDerived X) (hE : IsPerfect E)
    (xbar : GeometricPoint X) :
    Set.Finite (setOf fun i : ℤ ↦ ¬ IsZero (fiberHomology E xbar i)) := sorry

/-- The Euler characteristic of the derived residue-field fibers of a perfect derived
module on an algebraic space is locally constant on `Points X`. -/
theorem fiberEulerChar_isLocallyConstant (E : ModuleDerived X) (hE : IsPerfect E) :
    IsLocallyConstant (fiberEulerChar E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
