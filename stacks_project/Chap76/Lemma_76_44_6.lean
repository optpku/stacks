/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Conormal
import StacksCheckRecall

/-!
# Conormal criterion for quasi-regular immersions of algebraic spaces

An immersion of algebraic spaces is quasi-regular if and only if it is locally
of finite presentation, its conormal sheaf is finite locally free, and the
canonical comparison `ConormalAlgebra.symmetricToTotal` is an isomorphism.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.44.6: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Then `i` is a quasi-regular immersion if and only if
`i` is locally of finite presentation, the conormal sheaf `Hom.conormalSheaf i`
is finite locally free, and the canonical comparison
`ConormalAlgebra.symmetricToTotal i` is an isomorphism. -/
@[stacks 09RY] #check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.iff_locallyOfFinitePresentation_conormal :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    IsQuasiRegularImmersion i ↔
      LocallyOfFinitePresentation i ∧ (Hom.conormalSheaf i).IsFiniteLocallyFree ∧
        IsIso (ConormalAlgebra.symmetricToTotal i))

/- A quasi-regular immersion of algebraic spaces is locally of finite
presentation. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
      [IsQuasiRegularImmersion i], LocallyOfFinitePresentation i)

/- The conormal sheaf of a quasi-regular immersion of algebraic spaces is finite
locally free. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.isFiniteLocallyFree_conormalSheaf :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
      [IsQuasiRegularImmersion i], (Hom.conormalSheaf i).IsFiniteLocallyFree)

/- For a quasi-regular immersion of algebraic spaces, the canonical comparison
`ConormalAlgebra.symmetricToTotal i` is an isomorphism. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.isIso_symmetricToTotal :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
      [IsQuasiRegularImmersion i], IsIso (ConormalAlgebra.symmetricToTotal i))

/- An immersion of algebraic spaces that is locally of finite presentation,
whose conormal sheaf is finite locally free, and for which
`ConormalAlgebra.symmetricToTotal i` is an isomorphism, is a quasi-regular
immersion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.of_locallyOfFinitePresentation_conormal :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
      [LocallyOfFinitePresentation i] [(Hom.conormalSheaf i).IsFiniteLocallyFree]
      [IsIso (ConormalAlgebra.symmetricToTotal i)], IsQuasiRegularImmersion i)
