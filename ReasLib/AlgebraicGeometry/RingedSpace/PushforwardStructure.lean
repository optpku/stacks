module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# The pushed-forward structure sheaf of a ringed-space morphism

A morphism `f : X ⟶ Y` factors first through the ringed space on `Y` whose structure sheaf is
`f_* 𝒪_X`.  This leaf owns that intermediate target and the canonical morphism into it.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.PushforwardStructure

variable {X Y : RingedSpace.{u}}

/-- The ringed space `(Y, f_* 𝒪_X)` attached to a morphism `f : X ⟶ Y`. -/
@[stacks 01F3 "ringed space with pushed-forward structure sheaf"]
abbrev target (f : X ⟶ Y) : RingedSpace.{u} :=
  TopCat.Sheaf.toRingedSpace
    ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf)

/-- The canonical morphism `X ⟶ (Y, f_* 𝒪_X)` induced by `f`. -/
@[stacks 01F3 "morphism to the pushed-forward structure sheaf"]
abbrev lift (f : X ⟶ Y) : X ⟶ target f :=
  InducedCategory.homMk
    { base := f.hom.base
      c := 𝟙 _ }

/-- The global section ring of `(Y, f_* 𝒪_X)` is canonically isomorphic to the global section
ring of `X`. -/
@[stacks 01F3 "global sections of the pushed-forward structure sheaf"]
theorem globalSectionsRing_isIsomorphic (f : X ⟶ Y) :
    IsIsomorphic (RingedSpace.globalSectionsRing (target f))
      (RingedSpace.globalSectionsRing X) := sorry

end AlgebraicGeometry.RingedSpace.Hom.PushforwardStructure
