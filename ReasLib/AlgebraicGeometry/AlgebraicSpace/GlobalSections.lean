/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation

/-!
# Global sections of an algebraic space

The global-sections ring of an algebraic space is constructed as the equalizer of the two
restriction maps associated to a chosen étale presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Presentation

/-- The map on global sections induced by the first projection of a presentation. -/
noncomputable abbrev tAppTop {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X) :
    Γ(P.U.left, ⊤) ⟶ Γ(P.R.left.left, ⊤) :=
  P.R.t.left.appTop

/-- The map on global sections induced by the second projection of a presentation. -/
noncomputable abbrev sAppTop {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X) :
    Γ(P.U.left, ⊤) ⟶ Γ(P.R.left.left, ⊤) :=
  P.R.s.left.appTop

end Presentation

/-- A presentation of an algebraic space obtained from its structure atlas. -/
noncomputable def chosenPresentation {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presentation X :=
  let hU := Classical.choose_spec X.atlas
  let p := Classical.choose hU
  let h := Classical.choose_spec hU
  Presentation.ofAtlas p h.1 h.2

/-- The atlas of `chosenPresentation X` is the morphism selected from `X.atlas`. -/
theorem chosenPresentation_atlas {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (chosenPresentation X).atlas = Classical.choose (Classical.choose_spec X.atlas) :=
  sorry

/-- The ring of global sections of the structure sheaf, defined using a chosen presentation. -/
noncomputable def globalSectionsRing {S : Scheme.{u}} (X : AlgebraicSpace S) : CommRingCat.{u} :=
  equalizer (chosenPresentation X).tAppTop (chosenPresentation X).sAppTop

/-- The comparison map from the global-sections ring to global functions on the chosen atlas. -/
noncomputable abbrev globalSectionsRing_ι {S : Scheme.{u}} (X : AlgebraicSpace S) :
    globalSectionsRing X ⟶ Γ((chosenPresentation X).U.left, ⊤) :=
  equalizer.ι (chosenPresentation X).tAppTop (chosenPresentation X).sAppTop

/-- The two presentation restrictions agree after composing with the equalizer inclusion. -/
theorem globalSectionsRing_equalizes {S : Scheme.{u}} (X : AlgebraicSpace S) :
    globalSectionsRing_ι X ≫ (chosenPresentation X).tAppTop =
      globalSectionsRing_ι X ≫ (chosenPresentation X).sAppTop :=
  sorry

/-- Maps into the global-sections ring are equal if they agree after comparison with the atlas. -/
theorem globalSectionsRing_hom_ext {S : Scheme.{u}} {X : AlgebraicSpace S}
    {W : CommRingCat.{u}} {k l : W ⟶ globalSectionsRing X}
    (h : k ≫ globalSectionsRing_ι X = l ≫ globalSectionsRing_ι X) : k = l :=
  sorry

/-- On a representable algebraic space, the global-sections ring is isomorphic to that of the
presenting scheme. -/
theorem globalSectionsRing_ofOver {S : Scheme.{u}} (T : Over S) :
    Nonempty (globalSectionsRing (ofOver T) ≅ Γ(T.left, ⊤)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
