/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris

/-! # Mayer–Vietoris sequence and triangle for étale lower shriek -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

/- Lemma 75.10.1 (1). For an elementary distinguished square of algebraic spaces,
extension by zero of the intersection maps to the sum of the two extensions by
zero, giving a short exact sequence ending in any structure-sheaf module. -/
@[stacks 08GV] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisLowerShriek_shortExact :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
      [h : IsElementaryDistinguishedSquare j f] (F : X.Modules),
      -- Local instance justification (search instability): Extract the square's open-immersion certificate because class search for IsOpenImmersion j cannot determine the opposite leg f.
      letI : IsOpenImmersion j := h.isOpenImmersion
      -- Local instance justification (search instability): Extract the square's etale certificate because class search for Etale f cannot determine the opposite leg j.
      letI : Etale f := h.isEtale
      (mayerVietorisLowerShriekShortComplex j f F).ShortExact)

/- Lemma 75.10.1 (2). For every object of the derived category of structure-sheaf
modules, extension by zero along an elementary distinguished square gives the
corresponding distinguished triangle, with connecting morphism to the intersection
term shifted by positive one. -/
@[stacks 08GV] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisLowerShriek_mem_distTriang :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
      [h : IsElementaryDistinguishedSquare j f] (E : ModuleDerived X),
      -- Local instance justification (search instability): Extract the square's open-immersion certificate because class search for IsOpenImmersion j cannot determine the opposite leg f.
      letI : IsOpenImmersion j := h.isOpenImmersion
      -- Local instance justification (search instability): Extract the square's etale certificate because class search for Etale f cannot determine the opposite leg j.
      letI : Etale f := h.isEtale
      mayerVietorisLowerShriekTriangle j f E
          (mayerVietorisLowerShriekCochain_shortExact j f
            (DerivedCategory.Q.objPreimage E)) ∈
        distTriang (ModuleDerived X))
