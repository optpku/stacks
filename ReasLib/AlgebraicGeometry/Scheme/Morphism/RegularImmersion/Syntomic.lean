/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An immersion into a scheme smooth over a base is a regular immersion when its composite
to the base is syntomic. -/
theorem isRegularImmersion_of_syntomic_of_smooth_of_isImmersion
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (p : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] (hcomm : i ≫ f = p) (hp : Syntomic p) (hf : Smooth f) :
    IsRegularImmersion i := sorry

/-- An immersion between schemes smooth over the same base is a regular immersion. -/
theorem isRegularImmersion_of_smooth_of_smooth_of_isImmersion
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (p : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] (hcomm : i ≫ f = p) (hp : Smooth p) (hf : Smooth f) :
    IsRegularImmersion i := sorry

end AlgebraicGeometry
