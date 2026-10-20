/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Yoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/-!
# The morphism `hat x` of predeformation categories

Stacks tag 07XE: 2-Yoneda sends an object `x` over `U` to a 1-morphism
`(Sch/U)_fppf ⟶ 𝒳`, which induces a morphism of predeformation categories
`hat x : ℱ_{(Sch/U)_fppf, κ(u0), u0} ⟶ ℱ_{𝒳, κ(u0), x0}` over `C_Λ`.
-/

/- 98.12.1.1: given a locally Noetherian scheme `S`, a morphism `U ⟶ S` locally of
finite type, a finite type point `u0` of `U` with residue field `k = κ(u0)`, a
category `𝒳` fibred in groupoids over `(Sch/S)_fppf`, and an object `x` of `𝒳`
over `U`, 2-Yoneda sends `x` to a 1-morphism `(Sch/U)_fppf ⟶ 𝒳` and thereby
induces a morphism of predeformation categories
`hat x : ℱ_{(Sch/U)_fppf, k, u0} ⟶ ℱ_{𝒳, k, x0}` over `C_Λ`. -/
@[stacks 07XE]
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.hat :
  ∀ {S : Scheme} [IsLocallyNoetherian S] {Λ : Type} [CommRing Λ]
    [IsNoetherianRing Λ]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (U : Over S) (u0 : U.left)
    [Algebra Λ (AlgebraicGeometry.GroupoidsOver.Predeformation.residueType U u0)]
    [Module.Finite Λ (AlgebraicGeometry.GroupoidsOver.Predeformation.residueType U u0)]
    (kToS : Spec (CommRingCat.of
      (AlgebraicGeometry.GroupoidsOver.Predeformation.residueType U u0)) ⟶ S)
    [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ
        (AlgebraicGeometry.GroupoidsOver.Predeformation.residueType U u0))) ≫
          openImmersion = kToS)
    (h_kToS : kToS =
      AlgebraicGeometry.GroupoidsOver.Predeformation.residuePointToS U u0)
    (X : FiberedCategoryOver.Groupoids (Over S)) (x : X.p.Fiber U)
    [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0],
    AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation openImmersion
        h_factor (FiberedCategoryOver.Groupoids.slice U)
        (AlgebraicGeometry.GroupoidsOver.Predeformation.residueFiber U u0 kToS h_kToS) ⥤ᵇ
      AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation openImmersion
        h_factor X
        (AlgebraicGeometry.GroupoidsOver.Predeformation.residueObject U u0 kToS h_kToS X x))
