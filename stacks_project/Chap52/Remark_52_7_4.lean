/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalFunctions

open CategoryTheory RingedSite.Hom.ModuleDerived

universe u

/- Remark 52.7.4 records references concerning derived forms of the theorem on formal
functions, including the derived formal functions theorem for proper maps discussed in
Lurie's thesis, DAG XII, and Gaitsgory–Rozenblyum, as well as an analogue of the
formal-functions statement for complexes of quasi-coherent modules in
Halpern-Leistner–Preygel. The checked contextual theorem is the single-module result
above; the cited extension to complexes is not asserted here. -/
@[stacks 0AKL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion.pushforwardSingle :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData)
      [I.toModule.IsQuasicoherent],
      (hI : I.IsFiniteType) → (F : X.Modules) → [F.IsQuasicoherent] →
      ∀ {Khat : DerivedCategory X.Modules},
        (η : (DerivedCategory.singleFunctor X.Modules 0).obj F ⟶ Khat) →
        IsDerivedCompletion.{u, u, u, u} (I.comap f).toSubobject η →
        IsDerivedCompletion.{u, u, u, u} I.toSubobject
          ((AlgebraicGeometry.RingedSpace.moduleDerivedPushforward f.toShHom).map η))
