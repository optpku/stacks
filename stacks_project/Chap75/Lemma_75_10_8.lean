/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Glueing
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

/- Lemma 75.10.8. Derived module objects with an overlap isomorphism on an
 elementary distinguished square glue to a global object with compatible
 restriction isomorphisms. For these same isomorphisms, compatible morphisms
 into restrictions of a global object extend to a global morphism. -/
@[stacks 08HB] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_moduleDerivedGlue :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
      (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
      [IsElementaryDistinguishedSquare j f]
      (A : ModuleDerived U) (B : ModuleDerived V)
      (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
        (restrictFunctorDerived (Limits.pullback.snd j f)).obj B),
      ∃ (F : ModuleDerived X)
        (eU : (restrictFunctorDerived j).obj F ≅ A)
        (eV : (restrictFunctorDerived f).obj F ≅ B),
        (c.hom =
          (restrictFunctorDerived (Limits.pullback.fst j f)).map eU.inv ≫
            (restrictFunctorDerivedOverlapIso j f F).hom ≫
            (restrictFunctorDerived (Limits.pullback.snd j f)).map eV.hom) ∧
        ∀ (E : ModuleDerived X) (a : A ⟶ (restrictFunctorDerived j).obj E)
          (b : B ⟶ (restrictFunctorDerived f).obj E),
          moduleDerivedGlueHomCompatible j f A B c E a b →
          ∃ φ : F ⟶ E,
            (restrictFunctorDerived j).map φ = eU.hom ≫ a ∧
              (restrictFunctorDerived f).map φ = eV.hom ≫ b)
