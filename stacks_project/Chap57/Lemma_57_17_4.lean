/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.CountableIsomorphismLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 57.17.4: for finite-type `K`-schemes `X` and `Y` over a finite-type
`K`-scheme `S`, a countable family of finite-type base changes with chosen
isomorphisms covers every `K`-rational point where the fibers are isomorphic. -/
@[stacks 0G0X]
#check (AlgebraicGeometry.Scheme.exists_countable_finiteType_baseChange_isos :
    ∀ {K : Type u} [Field K] [IsAlgClosed K]
      (S : SchemeOverField K) [Scheme.Hom.FiniteType S.hom]
      (X Y : Over S.left) [Scheme.Hom.FiniteType X.hom]
      [Scheme.Hom.FiniteType Y.hom],
      ∃ I : Type u, Countable I ∧
        ∃ (Sᵢ : I → SchemeOverField K)
          (pᵢ : (i : I) → Sᵢ i ⟶ S)
          (hSᵢ : (i : I) → Scheme.Hom.FiniteType (pᵢ i).left)
          (hᵢ : (i : I) →
            (Over.pullback (pᵢ i).left).obj X ≅
              (Over.pullback (pᵢ i).left).obj Y),
          ∀ s : SchemeOverField.point K ⟶ S,
            Nonempty ((Over.pullback s.left).obj X ≅
              (Over.pullback s.left).obj Y) →
              ∃ (i : I) (q : SchemeOverField.point K ⟶ Sᵢ i),
                q ≫ pᵢ i = s)

end AlgebraicGeometry.Scheme
