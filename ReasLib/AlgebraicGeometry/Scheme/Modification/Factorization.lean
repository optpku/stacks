/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Modification.Elementary

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A finite algebraic morphism with monic structure-sheaf map and finite exceptional
locus factors, up to endpoint isomorphisms, into elementary point-glueings and
tangent-vector squishings. -/
theorem existsElementaryModificationFactorization
    {k : Type u} [Field k] [IsAlgClosed k]
    (X X' : SchemeOverField k) [Algebraic X] [Algebraic X']
    (f : X' ⟶ X) [IsFinite f.left]
    [Mono (RingedSpace.Hom.commRingSheafPushforwardMap f.left.toShHom)]
    (U : X.left.Opens) [IsIso (f.left ∣_ U)]
    (hU : Set.Finite ((U : Set X.left)ᶜ)) :
    ∃ (n : ℕ) (D : ComposableArrows (SchemeOverField k) n)
      (e_source : X' ≅ D.left) (e_target : D.right ≅ X)
      (h_alg : ∀ i : Fin (n + 1), Algebraic (D.obj i)),
      e_source.hom ≫ D.hom ≫ e_target.hom = f ∧
        ∀ i : Fin n,
          @ElementaryModification k _ _
            (D.obj i.castSucc) (D.obj i.succ)
            (h_alg i.castSucc) (h_alg i.succ)
            (D.map' i.1 (i.1 + 1)) := sorry

end AlgebraicGeometry

end
