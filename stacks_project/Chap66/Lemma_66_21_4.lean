/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal
public import stacks_project.Chap66.Remark_66_7_6_LocalRing
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

/-!
# Reduced algebraic spaces

An algebraic space is reduced if and only if every local ring is reduced. In that case the
ring of global sections is reduced, and a global function vanishing everywhere is zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.21.4 (1): let `S` be a scheme and let `X` be an algebraic space over `S`. Then `X`
is reduced, in the sense of `hasEtaleLocal` for `IsReduced`, if and only if for every
`x : Points X` the local ring of `X` at `x` is reduced, in the sense of Remark 66.7.6
via `localRingHas`. -/
@[stacks 0BGS]
theorem isReduced_iff_localRingHas {S : Scheme.{u}} (X : AlgebraicSpace S) :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X ↔
      ∀ x : Points X, localRingHas (fun R ↦ _root_.IsReduced R) X x :=
  sorry

/-- Lemma 66.21.4 (2): if `X` is a reduced algebraic space, then `Γ(X, 𝒪_X)` is a reduced
ring. -/
@[stacks 0BGS]
theorem isReduced_globalSectionsRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X) :
    _root_.IsReduced (globalSectionsRing X) :=
  sorry

/-- Lemma 66.21.4 (3): if `X` is a reduced algebraic space and `f : Γ(X, 𝒪_X)` satisfies
`X = V(f)`, then `f = 0`. The hypothesis is encoded as the zero locus of the image of `f`
along `globalSectionsRing_ι` being the whole chosen étale atlas, matching the source’s
inclusion `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)` along a surjective étale atlas `U`. -/
@[stacks 0BGS]
theorem eq_zero_of_zeroLocus_eq_univ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X)
    (f : globalSectionsRing X)
    (hf : (chosenPresentation X).U.left.zeroLocus {(globalSectionsRing_ι X).hom f} =
      Set.univ) :
    f = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
