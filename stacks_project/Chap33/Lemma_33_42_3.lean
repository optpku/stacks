/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.GenericPointCriterion

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.42.3: let `f : T ⟶ X` be a morphism of schemes. If `T` is affine, `X` is
quasi-separated, `genericPoints X` is finite, `f` maps `genericPoints T` injectively into
`genericPoints X`, and `f` induces stalk isomorphisms at every point of a finite set `S`, then
the image of `S` is contained in an affine open of `X`. -/
@[stacks 09NI] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_containing_image_of_stalkMap_isIso :
    ∀ {T X : Scheme.{u}} (f : T ⟶ X) [IsAffine T] [QuasiSeparatedSpace X],
      (genericPoints X).Finite →
      Set.MapsTo f.base (genericPoints T) (genericPoints X) →
      Set.InjOn f.base (genericPoints T) →
      ∀ (S : Set T), S.Finite →
        (∀ t : T, t ∈ S → IsIso (f.stalkMap t)) →
        ∃ U : X.affineOpens, Set.image f.base S ⊆ ((U : X.Opens) : Set X))
