/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.66.1 (Definitions) -/
@[stacks 0H8Q] #check (AlgebraicGeometry.Scheme.PicardGroup :
  Scheme.{u} → Type (u + 1))

section
variable {X : Scheme.{u}} (F : X.Modules)

-- (1) Scheme
#check (Scheme.{u} : Type (u + 1))

-- (2) Quasi-coherent module
#check (F.IsQuasicoherent : Prop)

-- (3) Picard group
#check (X.PicardGroup : Type _)
#check (inferInstance : AddCommGroup X.PicardGroup)

end

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

-- (4) Pushforward
#check ((Scheme.Modules.pushforward f).obj F : Y.Modules)

#check Scheme.Modules.pushforward f

#check (Scheme.Modules.pushforward_obj_obj f F :
  ∀ U : Y.Opens, Γ((Scheme.Modules.pushforward f).obj F, U) = Γ(F, f ⁻¹ᵁ U))

end

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- (5) Closed immersion
#check (IsClosedImmersion f : Prop)

#check isClosedImmersion_iff

#check (IsClosedImmersion.iff_isPreimmersion (f := f) :
  IsClosedImmersion f ↔ IsPreimmersion f ∧ IsClosed (Set.range f))

end

section
variable {k : Type u} [Field k] (V : SchemeOverField k)

-- (6) Variety over a field
#check (Variety V : Prop)

#check (variety_iff V :
  Variety V ↔ IsIntegral V.left ∧ IsSeparated V.hom ∧ Scheme.Hom.FiniteType V.hom)

end
