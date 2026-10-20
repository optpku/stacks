/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.InverseImageDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 43.13.2 (1): if a regular immersion of varieties has codimension `c`, then every
irreducible component of the scheme-theoretic inverse image of a `d`-dimensional subvariety
has dimension at least `d - c`. -/
@[stacks 0AZN] #check
  (AlgebraicGeometry.SchemeOverField.componentDimension_lowerBound_of_regularImmersion :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Variety X] [Variety Y]
      (f : X ⟶ Y) (Z : Y.left.IdealSheafData)
      [Variety (Over.mk (Z.subschemeι ≫ Y.hom))]
      (d c : ℕ) (hZ : topologicalKrullDim Z.subscheme = (d : WithBot ℕ∞))
      [IsRegularImmersion f.left]
      [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf f.left)]
      (C : irreducibleComponents (Z.comap f.left).subscheme),
      ((d - c : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C)

/- Lemma 43.13.2 (2): if a local complete-intersection morphism of varieties has virtual
relative dimension `r`, then every irreducible component of the scheme-theoretic inverse
image of a `d`-dimensional subvariety has dimension at least `d + r`. -/
@[stacks 0AZN] #check
  (AlgebraicGeometry.SchemeOverField.componentDimension_lowerBound_of_localCompleteIntersection :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Variety X] [Variety Y]
      (f : X ⟶ Y) (Z : Y.left.IdealSheafData)
      [Variety (Over.mk (Z.subschemeι ≫ Y.hom))]
      (d : ℕ) (r : ℤ) (hZ : topologicalKrullDim Z.subscheme = (d : WithBot ℕ∞))
      (h_lci : LocalCompleteIntersectionOfRelativeDimension f.left r)
      (C : irreducibleComponents (Z.comap f.left).subscheme),
      (Int.toNat ((d : ℤ) + r) : WithBot ℕ∞) ≤ topologicalKrullDim C)

end AlgebraicGeometry.SchemeOverField
