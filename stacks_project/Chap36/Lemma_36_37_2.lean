/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.37.2: on a quasi-compact and quasi-separated scheme with the resolution property,
every perfect object of `D(𝒪_X)` is represented by a bounded complex of finite locally free
`𝒪_X`-modules. -/
@[stacks 0F8F] #check
  (AlgebraicGeometry.Scheme.exists_boundedFiniteLocallyFree_representative :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (hX : AlgebraicGeometry.Scheme.HasResolutionProperty X)
      (K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (hK : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect K),
      ∃ E : CochainComplex X.toRingedSpace.Modules ℤ,
        ∃ _ : K ≅ DerivedCategory.Q.obj E,
          SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree E)
