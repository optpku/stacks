/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import stacks_project.Chap65.Definition_65_9_3_Presentation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Global sections of the structure sheaf of an algebraic space

The ring `Γ(X, 𝒪_X)` is realized as the equalizer of the two restriction maps on global
functions along an étale presentation of `X`.
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

/-- The ring of global sections `Γ(X, 𝒪_X)`, as the equalizer of the two restrictions along a
chosen étale presentation. -/
noncomputable def globalSectionsRing {S : Scheme.{u}} (X : AlgebraicSpace S) : CommRingCat.{u} :=
  equalizer (chosenPresentation X).tAppTop (chosenPresentation X).sAppTop

/-- The comparison map from `Γ(X, 𝒪_X)` to global functions on the chosen atlas. -/
noncomputable abbrev globalSectionsRing_ι {S : Scheme.{u}} (X : AlgebraicSpace S) :
    globalSectionsRing X ⟶ Γ((chosenPresentation X).U.left, ⊤) :=
  equalizer.ι (chosenPresentation X).tAppTop (chosenPresentation X).sAppTop

/-- The two presentation restrictions agree after composing with the equalizer inclusion. -/
theorem globalSectionsRing_equalizes {S : Scheme.{u}} (X : AlgebraicSpace S) :
    globalSectionsRing_ι X ≫ (chosenPresentation X).tAppTop =
      globalSectionsRing_ι X ≫ (chosenPresentation X).sAppTop :=
  sorry

/-- Maps into `Γ(X, 𝒪_X)` are equal if they agree after the comparison map to the atlas. -/
theorem globalSectionsRing_hom_ext {S : Scheme.{u}} {X : AlgebraicSpace S}
    {W : CommRingCat.{u}} {k l : W ⟶ globalSectionsRing X}
    (h : k ≫ globalSectionsRing_ι X = l ≫ globalSectionsRing_ι X) : k = l :=
  sorry

/-- On a representable algebraic space, `Γ(X, 𝒪_X)` recovers the global-sections ring of the
presenting scheme. -/
theorem globalSectionsRing_ofOver {S : Scheme.{u}} (T : Over S) :
    Nonempty (globalSectionsRing (ofOver T) ≅ Γ(T.left, ⊤)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
