/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.DoubledOrigin

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FinitePart

universe u

/- Remark 79.12.12: the finite part of the doubled-origin fold is not an algebraic space. -/
@[stacks 04QI] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePart.not_isAlgebraicSpace_foldFinitePart :
    ∀ (k : Type u) [Field k],
      ¬ IsAlgebraicSpace (finitePart (AlgebraicGeometry.AlgebraicSpace.FinitePart.foldMorphism k)))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instLocallyOfFiniteType_foldMorphism :
  ∀ (k : Type u) [Field k], LocallyOfFiniteType (foldMorphism k))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.not_separated_foldMorphism :
  ∀ (k : Type u) [Field k], ¬ Separated (foldMorphism k))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.originPoint_ne :
  ∀ (k : Type u) [Field k], originPoint k 0 ≠ originPoint k 1)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.eq_pointOfSubset_iff :
  ∀ (k : Type u) [Field k], ∀ (p : Point (foldMorphism k) (originOver k)),
    p.a = originToY k ↔ ∃ s : Set (Fin 2), p = pointOfSubset k s)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.isEtaleLiftable_pointOfSubset_of_ne_univ :
  ∀ (k : Type u) [Field k], ∀ {s : Set (Fin 2)}
    (hs : s ≠ Set.univ),
    IsEtaleLiftable (pointOfSubset k s))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.not_isEtaleLiftable_univ :
  ∀ (k : Type u) [Field k], ¬ IsEtaleLiftable (pointOfSubset k (Set.univ : Set (Fin 2))))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.not_etale_foldFinitePart_of_isAlgebraicSpace :
  ∀ (k : Type u) [Field k], ∀ [IsAlgebraicSpace (finitePart (foldMorphism k))],
    ¬ Etale (foldFinitePartHom k))
