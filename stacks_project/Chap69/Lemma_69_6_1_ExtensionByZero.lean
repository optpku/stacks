/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerExtension

/-! Integer-module extension by zero and binary coproduct families. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.moduleExtensionByZeroInteger :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    Sheaf (smallEtaleTopology X) IntegerModuleCat)

#check (AlgebraicGeometry.AlgebraicSpace.moduleExtensionByZero :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f],
    Sheaf (smallEtaleTopology U) IntegerModuleCat ⥤
      Sheaf (smallEtaleTopology X) IntegerModuleCat)

#check (AlgebraicGeometry.AlgebraicSpace.finTwo :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → AlgebraicSpace S → Fin 2 → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.finTwoHom :
  ∀ {S : Scheme.{u}} {X U1 U2 : AlgebraicSpace S}
    (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) (i : Fin 2), finTwo U1 U2 i ⟶ X)
