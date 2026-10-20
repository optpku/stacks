/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Linearity of module sheaves on projective space

The base ring acts canonically on module sheaves over standard projective space through the
structure morphism and the induced action of global sections.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The base ring acts canonically on projective-space module sheaves through global sections. -/
noncomputable instance instLinearModules
    (A : Type u) [CommRing A] (n : ℕ) : Linear A (scheme A n).Modules :=
  Linear.ofRingMorphism
    ((RingedSpace.GlobalSections.centerHom (scheme A n).toRingedSpace).comp
      (globalSectionsComparison A n).hom)

/-- The derived category of projective-space module sheaves is canonically linear over the base
ring, extending the linearity of the underlying module category. -/
noncomputable instance instLinearModuleDerived
    (A : Type u) [CommRing A] (n : ℕ) :
    Linear A (RingedSpace.ModuleDerived (scheme A n).toRingedSpace) :=
  DerivedCategory.instLinear A (scheme A n).Modules

/-- Internal Hom on projective space over a field is linear over that field. -/
instance instLinear_ihom {k : Type u} [Field k] {d : ℕ} (F : (scheme k d).Modules) :
    (ihom F).Linear k := sorry

end AlgebraicGeometry.ProjectiveSpace

end
