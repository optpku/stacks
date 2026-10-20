/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoreticInvariant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- Lemma 83.5.9: in the situation of Definition 83.5.8, a morphism `φ : U ⟶ X` over `B` is
set-theoretically `R`-invariant if and only if for every algebraically closed field `k` over
`B` the induced map `U(k) → X(k)` is constant on geometric `R`-orbits. -/
@[stacks 048W] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticallyInvariant_iff_constantOnOrbits :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
      (P : PreRelation U) (φ : U ⟶ X),
    P.IsSetTheoreticallyInvariant φ ↔
      ∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
        y ∈ P.orbit kbar x → x ≫ φ = y ≫ φ)

/- A set-theoretically invariant morphism is constant on geometric `R`-orbits. -/
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.eq_comp_of_mem_orbit :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} (hφ : P.IsSetTheoreticallyInvariant φ)
    {kbar : GeometricPoint B} {x y : Over.mk kbar.hom ⟶ U} (h : y ∈ P.orbit kbar x),
    x ≫ φ = y ≫ φ)

end AlgebraicGeometry.AlgebraicSpace.PreRelation
