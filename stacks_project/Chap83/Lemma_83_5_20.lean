/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSpace.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- Lemma 83.5.20: Let `B ⟶ S` as in Section 83.2. Let `j = (t, s) : R ⟶ U ⨯ U` be a
pre-relation. Assume `R` and `U` are locally of finite type over `B`. Let `φ : U ⟶ X` be an
`R`-invariant morphism of algebraic spaces over `B`. Then `φ` is an orbit space for `R` if and
only if, for every geometric point `kbar` of `B`, the natural map
`Quot (P.weaklyEquivalent (Over.mk kbar.hom)) ⟶ (Over.mk kbar.hom ⟶ X)` is bijective. -/
@[stacks 04A0] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isOrbitSpace_iff_bijective_weaklyEquivalentQuotMap :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B} (P : PreRelation U)
      {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
      [LocallyOfFiniteType U.hom] [LocallyOfFiniteType P.left.hom],
      P.IsOrbitSpace φ ↔
        ∀ kbar : GeometricPoint B, Function.Bijective (P.weaklyEquivalentQuotMap hφ kbar))

end AlgebraicGeometry.AlgebraicSpace.PreRelation
