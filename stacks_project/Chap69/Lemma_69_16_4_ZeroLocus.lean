module

public import Mathlib.AlgebraicGeometry.Scheme
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

/-!
# Zero locus of global sections on an algebraic space

The vanishing locus `V(s) ⊂ |X|` of a set of global functions is the image of the
scheme-theoretic zero locus of their restrictions along a chosen étale atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Presentation

/-- The atlas of a presentation, as a morphism of algebraic spaces from the presenting
scheme. -/
abbrev spaceHom {S : Scheme.{u}} {F : AlgebraicSpace S} (P : Presentation F) :
    ofOver P.U ⟶ F :=
  P.atlas

/-- `spaceHom P` is the atlas morphism of `P`. -/
theorem spaceHom_eq {S : Scheme.{u}} {F : AlgebraicSpace S} (P : Presentation F) :
    P.spaceHom = P.atlas :=
  sorry

end Presentation

/-- The zero locus of a set of global sections of `𝒪_X`, as a subset of `Points X`. It is the
image of the scheme-theoretic zero locus of the restrictions to the chosen étale atlas. -/
def zeroLocus {S : Scheme.{u}} (X : AlgebraicSpace S) (s : Set (globalSectionsRing X)) :
    Set (Points X) :=
  Points.mapOfOver (chosenPresentation X).spaceHom ''
    ((chosenPresentation X).U.left.zeroLocus ((globalSectionsRing_ι X).hom '' s))

/-- Unfolding of `zeroLocus` as the image of the atlas scheme zero locus. -/
theorem zeroLocus_def {S : Scheme.{u}} (X : AlgebraicSpace S) (s : Set (globalSectionsRing X)) :
    X.zeroLocus s =
      Points.mapOfOver (chosenPresentation X).spaceHom ''
        ((chosenPresentation X).U.left.zeroLocus ((globalSectionsRing_ι X).hom '' s)) :=
  sorry

/-- A point of `X` lies in `X.zeroLocus s` if and only if it is the image of a point of the
chosen atlas lying in the scheme-theoretic zero locus of the restricted sections. -/
theorem mem_zeroLocus_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (s : Set (globalSectionsRing X)) (x : Points X) :
    x ∈ X.zeroLocus s ↔
      ∃ u : (chosenPresentation X).U.left,
        Points.mapOfOver (chosenPresentation X).spaceHom u = x ∧
          u ∈ (chosenPresentation X).U.left.zeroLocus ((globalSectionsRing_ι X).hom '' s) :=
  sorry

/-- The zero locus of a set of global sections is closed in `Points X`. -/
theorem isClosed_zeroLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    (s : Set (globalSectionsRing X)) : IsClosed (X.zeroLocus s) :=
  sorry

/-- The zero locus of a singleton `{f}` is the image of the atlas zero locus of the restricted
function. -/
theorem zeroLocus_singleton {S : Scheme.{u}} (X : AlgebraicSpace S) (f : globalSectionsRing X) :
    X.zeroLocus {f} =
      Points.mapOfOver (chosenPresentation X).spaceHom ''
        ((chosenPresentation X).U.left.zeroLocus {(globalSectionsRing_ι X).hom f}) :=
  sorry

/-- `X.zeroLocus {f}` is all of `Points X` if and only if the restricted function vanishes on the
whole chosen étale atlas, recovering the encoding of `X = V(f)` used in Lemma 66.21.4. -/
theorem zeroLocus_eq_univ_iff {S : Scheme.{u}} (X : AlgebraicSpace S) (f : globalSectionsRing X) :
    X.zeroLocus {f} = Set.univ ↔
      (chosenPresentation X).U.left.zeroLocus {(globalSectionsRing_ι X).hom f} = Set.univ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

