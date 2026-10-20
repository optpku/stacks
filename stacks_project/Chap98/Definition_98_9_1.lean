/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap98.Definition_98_9_1_AlgebraHom
public import stacks_project.Chap98.Definition_98_9_1_Hom

/-!
# Formal objects of a category fibred in groupoids over `(Sch/S)_fppf`

Stacks tag 07X4: a formal object of a category fibred in groupoids over a
locally Noetherian scheme is a complete local `S`-algebra together with a
forward system over its maximal-adic truncations; morphisms are natural
families, inducing a morphism of spectra over `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
variable {X : AlgebraicGeometry.GroupoidsOver S}

/- Definition 98.9.1 (1): for a locally Noetherian scheme `S` and a category
`X` fibred in groupoids over `(Sch/S)_fppf`, a formal object is a Noetherian
complete local `S`-algebra `R` with `R ⧸ m` of finite type over `S`, together
with objects `ξ_n` of `X` over `Spec(R ⧸ m^n)` and transitions
`ξ_n ⟶ ξ_{n+1}` over `Spec(R ⧸ m^n) ⟶ Spec(R ⧸ m^{n+1})`. Lean stage `n` is
the source object `ξ_{n+1}` over `Spec(R ⧸ m^{n+1})`. -/
@[stacks 07X4] #check (AlgebraicGeometry.GroupoidsOver.FormalObject :
  AlgebraicGeometry.GroupoidsOver S → Type (u + 1))

/- Definition 98.9.1 (2): a morphism of formal objects `a : ξ ⟶ η` is a
natural family `a_n : ξ_n ⟶ η_n`; applying `p` yields compatible truncated
spectra and hence `a0 : Spec(R) ⟶ Spec(T)` over `S`, over which `a` lies. -/
@[stacks 07X4] #check (AlgebraicGeometry.GroupoidsOver.FormalObject.Hom :
  AlgebraicGeometry.GroupoidsOver.FormalObject X →
    AlgebraicGeometry.GroupoidsOver.FormalObject X → Type u)

/- The induced scheme morphism `a0 : Spec(R) ⟶ Spec(T)`. -/
#check (AlgebraicGeometry.GroupoidsOver.FormalObject.Hom.overMorphism :
  ∀ {ξ η : AlgebraicGeometry.GroupoidsOver.FormalObject X},
    AlgebraicGeometry.GroupoidsOver.FormalObject.Hom ξ η →
      (Spec (CommRingCat.of ξ.base.carrier) ⟶ Spec (CommRingCat.of η.base.carrier)))

/- A morphism of formal objects lies over its induced morphism of spectra. -/
#check (AlgebraicGeometry.GroupoidsOver.FormalObject.Hom.liesOver :
  ∀ {ξ η : AlgebraicGeometry.GroupoidsOver.FormalObject X}
    (a : AlgebraicGeometry.GroupoidsOver.FormalObject.Hom ξ η),
    a.overMorphism ≫ η.base.toS = ξ.base.toS)
