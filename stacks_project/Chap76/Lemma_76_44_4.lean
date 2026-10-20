/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Noetherian
import StacksCheckRecall

/-!
# Regular immersions into locally Noetherian algebraic spaces

For an immersion of algebraic spaces into a locally Noetherian target,
Koszul-regular, `H₁`-regular, and quasi-regular immersions are equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.44.4: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Assume `X` is locally Noetherian. Then `i` is
Koszul-regular if and only if `i` is `H₁`-regular if and only if `i` is
quasi-regular. -/
@[stacks 09RW] #check (AlgebraicGeometry.AlgebraicSpace.immersionRegularity_tfae :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsImmersion i] [IsLocallyNoetherian X],
    List.TFAE
      [ IsKoszulRegularImmersion i
      , IsH1RegularImmersion i
      , IsQuasiRegularImmersion i ])

/- A quasi-regular immersion of algebraic spaces into a locally Noetherian
target is Koszul-regular. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.isKoszulRegular_of_isLocallyNoetherian :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsQuasiRegularImmersion i],
    IsKoszulRegularImmersion i)

/- For an immersion of algebraic spaces into a locally Noetherian target,
Koszul-regularity is equivalent to `H₁`-regularity. -/
#check (AlgebraicGeometry.AlgebraicSpace.isKoszulRegularImmersion_iff_isH1RegularImmersion :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsImmersion i] [IsLocallyNoetherian X],
    IsKoszulRegularImmersion i ↔ IsH1RegularImmersion i)

/- For an immersion of algebraic spaces into a locally Noetherian target,
`H₁`-regularity is equivalent to quasi-regularity. -/
#check (AlgebraicGeometry.AlgebraicSpace.isH1RegularImmersion_iff_isQuasiRegularImmersion :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    [IsImmersion i] [IsLocallyNoetherian X],
    IsH1RegularImmersion i ↔ IsQuasiRegularImmersion i)

end AlgebraicGeometry.AlgebraicSpace
