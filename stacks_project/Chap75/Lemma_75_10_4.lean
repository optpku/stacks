/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Hom
import StacksCheckRecall

/-!
# Mayer–Vietoris Hom sequence for derived modules on algebraic spaces

Lemma 75.10.4: an elementary distinguished square of algebraic spaces yields an
exact Hom/Ext segment in the unbounded derived categories of étale modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 75.10.4. Let `S` be a scheme. Let `(j : U ⟶ X, f : V ⟶ X)` be an
elementary distinguished square of algebraic spaces over `S`. For objects
`E`, `F` of `D(𝒪_X)` the Mayer–Vietoris Hom segment
`Ext⁽-1⁾(E|_W, F|_W) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊞ Hom(E|_V, F|_V) ⟶ Hom(E|_W, F|_W)`
is exact, where `W = U ×_X V` and subscripts denote étale restriction in the
relevant derived categories. -/
@[stacks 08H9]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisHomSequence_exact :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E F : ModuleDerived X),
    (mk₃
        (mayerVietorisHomδ j f E F
          (mayerVietorisLowerShriekδ j f E
            (mayerVietorisLowerShriekCochain_shortExact j f (DerivedCategory.Q.objPreimage E))))
        (mayerVietorisHomRestrict j f E F)
        (mayerVietorisHomDiff j f E F)).Exact)

end AlgebraicGeometry.AlgebraicSpace.Modules
