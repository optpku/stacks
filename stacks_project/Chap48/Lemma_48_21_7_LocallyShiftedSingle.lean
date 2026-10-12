/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.LocallyShiftedSingle

@[expose] public section

open CategoryTheory DerivedCategory TopologicalSpace

universe u

#check (LocallyConstant.fiberClopen :
  ∀ {X : Type u} [TopologicalSpace X], LocallyConstant X ℕ → ℕ → Clopens X)

#check (LocallyConstant.mem_fiberClopen :
  ∀ {X : Type u} [TopologicalSpace X] (d : LocallyConstant X ℕ) (n : ℕ) (x : X),
    x ∈ d.fiberClopen n ↔ d x = n)

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyShiftedSingle :
  ∀ {X : AlgebraicGeometry.RingedSpace.{u}},
    AlgebraicGeometry.RingedSpace.ModuleDerived X → X.Modules →
      LocallyConstant X ℕ → Prop)

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.isLocallyShiftedSingle_iff :
  ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
    (E : AlgebraicGeometry.RingedSpace.ModuleDerived X) (ω : X.Modules)
    (d : LocallyConstant X ℕ),
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyShiftedSingle E ω d ↔
      ∀ n : ℕ, IsIsomorphic
        ((AlgebraicGeometry.RingedSpace.moduleRestrictionToOpenDerived X
          (d.fiberClopen n).toOpens).obj
            (((singleFunctor X.Modules 0).obj ω)⟦(n : ℤ)⟧))
        ((AlgebraicGeometry.RingedSpace.moduleRestrictionToOpenDerived X
          (d.fiberClopen n).toOpens).obj E))

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyShiftedSingle.of_isIsomorphic :
  ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
    {E E' : AlgebraicGeometry.RingedSpace.ModuleDerived X} {ω : X.Modules}
    {d : LocallyConstant X ℕ},
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyShiftedSingle E ω d →
      IsIsomorphic E E' →
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyShiftedSingle E' ω d)
