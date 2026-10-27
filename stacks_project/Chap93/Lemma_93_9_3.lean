/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TangentExt
import StacksCheckRecall

/-!
# Infinitesimal automorphisms and tangent space of `Def_X`

For a scheme over `k`, infinitesimal automorphisms identify with degree-zero
cotangent extensions, morphisms from differentials, and relative derivations.
The tangent space identifies with degree-one cotangent extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))

/- Lemma 93.9.3 (1)
Infinitesimal automorphisms identify with degree-zero cotangent extensions. -/
@[stacks 0DY9] #check (FlatSchemeCat.infToExtZero_bijective Λ k X hX :
  Function.Bijective (FlatSchemeCat.infToExtZero Λ k X hX))

/- Lemma 93.9.3 (2)
Degree-zero cotangent extensions identify with morphisms from differentials. -/
@[stacks 0DY9] #check (FlatSchemeCat.extZeroEquivHomOmega k X hX :
  FlatSchemeCat.extZero k X hX ≃
    (Ω[hX.toShHom] ⟶ SheafOfModules.unit X.toRingedSpace.ringCatSheaf))

/- Lemma 93.9.3 (3)
Morphisms from differentials identify with relative derivations. -/
@[stacks 0DY9] #check (AlgebraicGeometry.RingedSpace.Hom.homEquiv hX.toShHom
    (SheafOfModules.unit X.toRingedSpace.ringCatSheaf) :
  (Ω[hX.toShHom] ⟶ SheafOfModules.unit X.toRingedSpace.ringCatSheaf) ≃
    AlgebraicGeometry.RingedSpace.Hom.derivations hX.toShHom
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))

/- Lemma 93.9.3 (4)
Tangent classes identify with degree-one cotangent extensions. -/
@[stacks 0DY9] #check (FlatSchemeCat.ofExtOne_bijective Λ k X hX :
  Function.Bijective (FlatSchemeCat.ofExtOne Λ k X hX))
