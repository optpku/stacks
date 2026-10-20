/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules)

/- Companion checks for Exercise 111.59.1 (Definitions) (1): the scheme-theoretic
fibre of `f` at `y : Y` is `f.fiber y`, the pullback of `f` along
`Y.fromSpecResidueField y`. -/
#check (AlgebraicGeometry.Scheme.Hom.fiber f y : Scheme)

#check (AlgebraicGeometry.Scheme.Hom.fiberι f y : f.fiber y ⟶ X)

#check (AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField f y :
  f.fiber y ⟶ Spec (Y.residueField y))

#check (AlgebraicGeometry.Scheme.Hom.fiber_fac f y :
  f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y)

/- Companion checks for Exercise 111.59.1 (Definitions) (2): `f` is a finite
morphism. -/
#check (AlgebraicGeometry.IsFinite f : Prop)

#check (AlgebraicGeometry.isFinite_iff f :
  AlgebraicGeometry.IsFinite f ↔
    IsAffineHom f ∧
      ∀ U : Y.Opens, IsAffineOpen U → (f.app U).hom.Finite)

/- Companion check for Exercise 111.59.1 (Definitions) (3): a quasi-coherent
`𝒪_X`-module. -/
#check (SheafOfModules.IsQuasicoherent F : Prop)

section
variable {k : Type u} [Field k] (V : SchemeOverField k)

/- Exercise 111.59.1 (Definitions). This exercise requests six independent definitions.
The following numbered companion checks supply them; this tagged check is item (4),
the existing ReasLib notion of variety, and does not encode the other five concepts. -/
@[stacks 0DT0] #check (AlgebraicGeometry.Variety : AlgebraicGeometry.SchemeOverField k → Prop)

#check (AlgebraicGeometry.Variety V : Prop)

#check (AlgebraicGeometry.variety_iff V :
  AlgebraicGeometry.Variety V ↔
    IsIntegral V.left ∧ IsSeparated V.hom ∧ Scheme.Hom.FiniteType V.hom)

end

/- Companion checks for Exercise 111.59.1 (Definitions) (5): `f` is a smooth
morphism. -/
#check (AlgebraicGeometry.Smooth f : Prop)

#check (AlgebraicGeometry.smooth_iff (f := f) :
  AlgebraicGeometry.Smooth f ↔
    ∀ {U : Y.Opens}, IsAffineOpen U →
      ∀ {V : X.Opens}, IsAffineOpen V →
        ∀ (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.Smooth)

/- Companion checks for Exercise 111.59.1 (Definitions) (6): `f` is a proper
morphism. -/
#check (AlgebraicGeometry.IsProper f : Prop)

#check (AlgebraicGeometry.isProper_iff (f := f) :
  AlgebraicGeometry.IsProper f ↔
    IsSeparated f ∧ UniversallyClosed f ∧ LocallyOfFiniteType f)
