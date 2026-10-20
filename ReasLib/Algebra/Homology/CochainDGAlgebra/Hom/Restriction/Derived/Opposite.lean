/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Coherence
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived restriction along opposite DGA maps

This leaf combines the functorial coherence of derived restriction with the canonical
identity and composition laws for opposite cochain-DGA homomorphisms.  It keeps transports
through `CochainDGAlgebra.oppositeFunctor` out of downstream statements about left modules.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory

namespace CochainDGAlgebra.Hom.Derived

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, x} R}

/-- Derived restriction along the opposite of an identity map is canonically the identity
functor on modules over the opposite DGA. -/
@[stacks 0GZI "identity coherence for derived restriction along opposite DGA maps"]
noncomputable def opRestrictionIdIso (A : CochainDGAlgebra.{u, x} R) :
    𝟭 (DifferentialGradedModule.Derived.Category.{u, v} A.opposite) ≅
      restriction ((CochainDGAlgebra.oppositeFunctor R).map
        (𝟙 A : CochainDGAlgebra.Hom A A)) :=
  restrictionIdIso.{u, x, v} A.opposite ≪≫
    eqToIso (congrArg restriction
      ((CochainDGAlgebra.oppositeFunctor R).map_id A).symm)

/-- Successive restrictions along opposite maps agree with restriction along the opposite of
their composite. -/
@[stacks 0GZI "composition coherence for derived restriction along opposite DGA maps"]
noncomputable def opRestrictionCompIso (f : A ⟶ B) (g : B ⟶ C) :
    restriction g.opposite ⋙ restriction f.opposite ≅
      restriction ((f ≫ g).opposite) :=
  restrictionCompIso.{u, x, v} f.opposite g.opposite ≪≫
    eqToIso (congrArg restriction
      (CochainDGAlgebra.Hom.opposite_comp g f).symm)

end CochainDGAlgebra.Hom.Derived
