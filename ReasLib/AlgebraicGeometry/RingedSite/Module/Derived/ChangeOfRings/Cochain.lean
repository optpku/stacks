/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings

/-! Total derived extension of scalars on cochain complexes of sheaves of modules. -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.SameSite

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; the generic homotopy-to-derived functor must use the same canonical derived-category dictionary as `ModuleDerived`.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, z}] [UnivLE.{w, z}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable {O O' : Sheaf J CommRingCat.{w}}

/-- Extension of scalars along a morphism of commutative ring sheaves admits a total left
derived functor for the generic homotopy-to-derived presentation on unbounded cochain complexes. -/
instance homotopyToDerivedHasLeftDerived (α : O ⟶ O') :
    Functor.HasLeftDerivedFunctor
      (Functor.Homotopy.toDerived ((sameSiteHom α).modulePullback.{z}))
      (HomotopyCategory.quasiIso
        (RingedSite.ModuleCat.{z} (RingedSite.ofCommRingSheaf J O)) (ComplexShape.up ℤ)) :=
  modulePullbackToDerivedHasLeftDerived α

end SheafOfModules.RingedSite.SameSite
