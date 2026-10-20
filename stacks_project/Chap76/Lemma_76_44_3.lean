/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications
import StacksCheckRecall

/-!
# Implications among regular immersions of algebraic spaces

A Koszul-regular immersion of algebraic spaces is `H₁`-regular, and an
`H₁`-regular immersion is quasi-regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.44.3 (1): Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. If `i` is Koszul-regular, then `i` is `H₁`-regular. -/
@[stacks 06BP] #check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.isH1Regular :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsKoszulRegularImmersion i],
    IsH1RegularImmersion i)

/- Lemma 76.44.3 (2): Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. If `i` is `H₁`-regular, then `i` is quasi-regular. -/
@[stacks 06BP] #check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.isQuasiRegular :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsH1RegularImmersion i],
    IsQuasiRegularImmersion i)

end AlgebraicGeometry.AlgebraicSpace
