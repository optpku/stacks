/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableDeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import stacks_project.Chap109.Lemma_109_22_7_Substack

/-!
# Stable moduli stacks as open DM substacks of `𝒞urves^{DM}`

The algebraic stacks `ℳ̄` and `ℳ̄_g` (`g ≥ 2`) are open substacks of
`𝒞urves^{DM}`. In particular they are DM, and they are Deligne–Mumford
stacks in the Hom-universe of `toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.22.7 (1): the moduli stack `ℳ̄` of stable curves is an open
substack of `𝒞urves^{DM}`, hence DM in the sense of Morphisms of Stacks,
Definition 101.4.2. -/
@[stacks 0E7A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.stable_le_dm :
  ∀ (S : Scheme.{u}), stable S ≤ dm S)

/- Lemma 109.22.7 (2): for `2 ≤ g`, the moduli stack `ℳ̄_g` of stable
curves of genus `g` is an open substack of `𝒞urves^{DM}`, hence DM in the
sense of Morphisms of Stacks, Definition 101.4.2. -/
@[stacks 0E7A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.stableOfGenus_le_dm :
  ∀ (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}), stableOfGenus g S ≤ dm S)

/- Lemma 109.22.7 (3): `ℳ̄` is a Deligne–Mumford stack in the sense of
Algebraic Stacks, Definition 94.12.2: it admits a scheme atlas which is
representable by algebraic spaces, étale, and surjective. -/
@[stacks 0E7A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_etale_surjective_atlas_stable :
  ∀ (S : Scheme.{u}),
    ∃ (U : Over S) (p : Classifying.slice U ⟶ ofObjectProperty (stable S)),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        CohStack.Hom.has (@AlgebraicSpace.Etale S) p ∧
          Classifying.Surjective p)

/- Lemma 109.22.7 (4): for `2 ≤ g`, the stack `ℳ̄_g` is a Deligne–Mumford
stack in the sense of Algebraic Stacks, Definition 94.12.2: it admits a
scheme atlas which is representable by algebraic spaces, étale, and
surjective. -/
@[stacks 0E7A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_etale_surjective_atlas_stableOfGenus :
  ∀ (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}),
    ∃ (U : Over S)
      (p : Classifying.slice U ⟶ ofObjectProperty (stableOfGenus g S)),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        CohStack.Hom.has (@AlgebraicSpace.Etale S) p ∧
          Classifying.Surjective p)

/- The stable loci are open substacks with unramified diagonals. -/
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsOpenDMSubstack_stable :
  ∀ (S : Scheme.{u}), IsOpenDMSubstack (stable S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsOpenDMSubstack_stableOfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}), IsOpenDMSubstack (stableOfGenus g S))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
