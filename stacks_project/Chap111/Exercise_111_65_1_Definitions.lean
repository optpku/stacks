/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.Carrier
public import ReasLib.AlgebraicGeometry.Scheme.ClosedPointDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Definition
public import ReasLib.NumberTheory.Height.Projectivization
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.FieldTheory.Cr
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.65.1 (Definitions) (1) -/
@[stacks 0GY9] #check (AlgebraicGeometry.SchemeObject.{u} : Type (u + 1))

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

/- Exercise 111.65.1 (Definitions) (2) -/
@[stacks 0GY9] #check (SheafOfModules.isQuasicoherentModule F : Prop)

/- Exercise 111.65.1 (Definitions) (3) -/
@[stacks 0GY9] #check (AlgebraicGeometry.isFlatMorphism f : Prop)

#check flat_iff

/- Exercise 111.65.1 (Definitions) (4) -/
@[stacks 0GY9] #check (AlgebraicGeometry.Scheme.IsFinite f : Prop)

#check (isFinite_iff f :
  IsFinite f ↔
    IsAffineHom f ∧
      ∀ U : Y.Opens, IsAffineOpen U → (f.app U).hom.Finite)

end

section
variable (S : Scheme.{u})

/- Exercise 111.65.1 (Definitions) (5) -/
@[stacks 0GY9] #check (AlgebraicGeometry.GroupScheme S : Type (u + 1))

#check (Grp (Over S) : Type (u + 1))

end

section
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/- Exercise 111.65.1 (Definitions) (6) -/
@[stacks 0GY9] #check (AlgebraicGeometry.Scheme.Hom.HasVarietyFibers f : Prop)

#check (f.fiber s : Scheme)
#check (f.fiberι s : f.fiber s ⟶ X)
#check (f.fiberToSpecResidueField s : f.fiber s ⟶ Spec (S.residueField s))

end

section
variable {k : Type u} [Field k] (V : SchemeOverField k)

#check (Variety V : Prop)

#check (variety_iff V :
  Variety V ↔ IsIntegral V.left ∧ IsSeparated V.hom ∧ Scheme.Hom.FiniteType V.hom)

end

section
variable {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
variable (x : closedPoints X.left)

/- Exercise 111.65.1 (Definitions) (7) -/
@[stacks 0GY9] #check (AlgebraicGeometry.Scheme.Hom.closedPointDegree X x : ℕ)

end

section
variable (n : ℕ) (p : Projectivization ℚ (Fin (n + 1) → ℚ))

/- Exercise 111.65.1 (Definitions) (8) -/
@[stacks 0GY9] #check (Projectivization.rationalLogHeight n p : ℝ)

#check Projectivization.logHeight_mk

#check Rat.logHeight_eq_max_abs_of_gcd_eq_one

end

section
variable (K : Type u) [Field K] (i : ℕ)

/- Exercise 111.65.1 (Definitions) (9) -/
@[stacks 0GY9] #check (Field.IsCr K i : Prop)

#check Field.isCr_iff

end
