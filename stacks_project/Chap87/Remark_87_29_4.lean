/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteTypeInverseSystem.Generators
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineSpace

/-!
# Affine space over a McQuillan affine formal algebraic space

Let `A` be a weakly admissible topological ring and `X = Spf(A)`, a McQuillan
affine formal algebraic space. A morphism `Y ⟶ X` of affine formal algebraic
spaces need not have McQuillan source.

Closed immersions are McQuillan and correspond to taut continuous maps
`φ : A →+* B` with closed kernel and dense image (Lemma 87.27.5). Whether
`B` equals the weak-ideal completion of `A ⧸ K` as in Example 87.27.6, and
whether such maps are surjective and open, is left open.

Finite-type morphisms correspond to objects `(B_I)` of
`FiniteTypeInverseSystem` by Lemma 87.29.3, and those stages are generated
over `A ⧸ I` by a uniform number of elements; whether the inverse-limit
projections are surjective is left open.

If `Y` is also McQuillan then `φ` is taut and topologically of finite type
(Lemma 87.29.2), so the morphism factors as a closed immersion
`Y ⟶ affineSpace hA r ⟶ Spf(A)`. The questions above are deferred to the
countably indexed case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Remark 87.29.4 (3): The finite-type quotient-algebra stages over a weakly
admissible ring admit a uniform finite bound on their numbers of generators. -/
@[stacks 0AJK] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.FiniteTypeInverseSystem.exists_uniform_generators :
    ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsWeaklyAdmissibleRing A] (B : FiniteTypeInverseSystem A),
      ∃ r : ℕ, ∀ I : (WeakIdealOfDefinition A)ᵒᵖ,
        ∃ f : MvPolynomial (Fin r) (A ⧸ I.unop.ideal) →ₐ[A ⧸ I.unop.ideal]
            B.obj.right.obj I,
          Function.Surjective f)

/- Remark 87.29.4 (4): A finite-type morphism with McQuillan source factors as
a closed immersion into affine space followed by the canonical projection. -/
@[stacks 0AJK] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.exists_closedImmersion_affineSpace :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      {Y : (Over S)ᵒᵖ ⥤ Type u} [IsMcQuillanAffine Y]
      (f : Y ⟶ (spf A hA).obj) [FiniteType f],
      ∃ r : ℕ, ∃ i : Y ⟶ (affineSpace hA r).obj,
        ClosedImmersion i ∧
          i ≫ (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
              (affineSpace.proj hA r) = f)
