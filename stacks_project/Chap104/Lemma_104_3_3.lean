module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import stacks_project.Chap103.Lemma_103_16_4
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Lemma 104.3.3

If `H` is a quasi-coherent module on the lisse-étale (resp. flat-fppf) site of
an algebraic stack `X`, then every cohomology sheaf of `Lg_! H` is locally
quasi-coherent and has the flat base change property on `X`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open ComplexShape RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The standard derived-category structure on lisse-étale `𝒪`-modules. -/
instance lisseEtaleModules_hasDerivedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleStructureSheaf X))

/-- The standard derived-category structure on flat-fppf `𝒪`-modules. -/
instance flatFppfModules_hasDerivedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  HasDerivedCategory.standard (SheafOfModules.{u} (flatFppfStructureSheaf X))

/-- Lisse-étale module lower shriek is additive. -/
instance lisseEtaleModuleLowerShriek.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleModuleLowerShriek X).Additive :=
  moduleLowerShriek.additive (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Flat-fppf module lower shriek is additive. -/
instance flatFppfModuleLowerShriek.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfModuleLowerShriek X).Additive :=
  moduleLowerShriek.additive (flatFppfInclusion X) (structureSheaf X)

namespace lisseEtaleModuleLowerShriek

/-- Homotopy-to-derived presentation of lisse-étale module lower shriek. -/
abbrev toDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    HomotopyCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ) ⥤
      ModuleDerivedEtale X :=
  (lisseEtaleModuleLowerShriek X).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-to-derived lisse-étale module lower shriek has a total left
derived functor. -/
instance toDerived.hasLeftDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.HasLeftDerivedFunctor (toDerived X)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ)) :=
  sorry

/-- Derived module lower shriek from the lisse-étale site to
`D(X_étale, 𝒪_X)`. -/
abbrev derived (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) ⥤
      ModuleDerivedEtale X :=
  Functor.totalLeftDerived (toDerived X) DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ))

/-- `Lg_!` of a lisse-étale module, viewed as an object of `D(X_étale, 𝒪_X)`. -/
abbrev singleDerived (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :
    ModuleDerivedEtale X :=
  (derived X).obj
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (0 : ℤ)).obj H)

/-- Degree-`p` cohomology of `Lg_! H` on the associated étale site. -/
abbrev homology (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (p : ℤ) :
    etaleModules X :=
  (DerivedCategory.homologyFunctor (etaleModules X) p).obj (singleDerived X H)

end lisseEtaleModuleLowerShriek

namespace flatFppfModuleLowerShriek

/-- Homotopy-to-derived presentation of flat-fppf module lower shriek. -/
abbrev toDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    HomotopyCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ) ⥤
      ModuleDerived X :=
  (flatFppfModuleLowerShriek X).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-to-derived flat-fppf module lower shriek has a total left
derived functor. -/
instance toDerived.hasLeftDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.HasLeftDerivedFunctor (toDerived X)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ)) :=
  sorry

/-- Derived module lower shriek from the flat-fppf site to `D(𝒪_X)`. -/
abbrev derived (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) ⥤
      ModuleDerived X :=
  Functor.totalLeftDerived (toDerived X) DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ))

/-- `Lg_!` of a flat-fppf module, viewed as an object of `D(𝒪_X)`. -/
abbrev singleDerived (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) :
    ModuleDerived X :=
  (derived X).obj
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (0 : ℤ)).obj H)

/-- Degree-`p` cohomology of `Lg_! H` on the fppf site of `X`. -/
abbrev homology (X : GroupoidsOver S) [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) (p : ℤ) :
    fppfModules X :=
  (DerivedCategory.homologyFunctor (fppfModules X) p).obj (singleDerived X H)

end flatFppfModuleLowerShriek

/-- Lemma 104.3.3 (1): let `X` be an algebraic stack, and let `H` be a
quasi-coherent `𝒪_{X_lisse,étale}`-module. For all `p : ℤ` the sheaf
`H^p(Lg_! H)` is a locally quasi-coherent module with the flat base change
property on `X`. -/
@[stacks 07B3]
theorem lisseEtaleModuleLowerShriek.homology_mem_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    lqcohFbc X (lisseEtaleModuleLowerShriek.homology X H p) :=
  sorry

/-- Source-semantic unfolding of Lemma 104.3.3 (1): the cohomology sheaf is
locally quasi-coherent and has the flat base change property. -/
theorem lisseEtaleModuleLowerShriek.homology_spec
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent (lisseEtaleModuleLowerShriek.homology X H p) ∧
      HasFlatBaseChange (lisseEtaleModuleLowerShriek.homology X H p) :=
  sorry

/-- Degree-`p` cohomology of `Lg_! H` on the lisse-étale comparison is locally
quasi-coherent. -/
instance lisseEtaleModuleLowerShriek.homology.instIsLocallyQuasiCoherent
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent (lisseEtaleModuleLowerShriek.homology X H p) :=
  sorry

/-- Degree-`p` cohomology of `Lg_! H` on the lisse-étale comparison has the
flat base change property. -/
instance lisseEtaleModuleLowerShriek.homology.instHasFlatBaseChange
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    HasFlatBaseChange (lisseEtaleModuleLowerShriek.homology X H p) :=
  sorry

/-- `Lg_! H` has cohomology in étale `LQCoh^{fbc}` for quasi-coherent lisse-étale
`H`. -/
theorem lisseEtaleModuleLowerShriek.singleDerived_cohomologyIn_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    [H.IsQuasicoherent] :
    DerivedCategory.cohomologyIn (lqcohFbc X)
      (lisseEtaleModuleLowerShriek.singleDerived X H) :=
  sorry

/-- Lemma 104.3.3 (2): let `X` be an algebraic stack, and let `H` be a
quasi-coherent `𝒪_{X_flat,fppf}`-module. For all `p : ℤ` the sheaf
`H^p(Lg_! H)` is a locally quasi-coherent module with the flat base change
property on `X`. -/
@[stacks 07B3]
theorem flatFppfModuleLowerShriek.homology_mem_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    FppfModules.lqcohFbc X (flatFppfModuleLowerShriek.homology X H p) :=
  sorry

/-- Source-semantic unfolding of Lemma 104.3.3 (2): the étale restriction of
the cohomology sheaf is locally quasi-coherent and has the flat base change
property. -/
theorem flatFppfModuleLowerShriek.homology_spec
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent
        ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) ∧
      HasFlatBaseChange
        ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) :=
  sorry

/-- Degree-`p` cohomology of `Lg_! H` on the flat-fppf comparison is locally
quasi-coherent after étale restriction. -/
instance flatFppfModuleLowerShriek.homology.instIsLocallyQuasiCoherent
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    IsLocallyQuasiCoherent
      ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) :=
  sorry

/-- Degree-`p` cohomology of `Lg_! H` on the flat-fppf comparison has the
flat base change property after étale restriction. -/
instance flatFppfModuleLowerShriek.homology.instHasFlatBaseChange
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] (p : ℤ) :
    HasFlatBaseChange
      ((restriction X).obj (flatFppfModuleLowerShriek.homology X H p)) :=
  sorry

/-- `Lg_! H` has cohomology in fppf `LQCoh^{fbc}` for quasi-coherent flat-fppf
`H`. -/
theorem flatFppfModuleLowerShriek.singleDerived_cohomologyIn_lqcohFbc
    {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
    [H.IsQuasicoherent] :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)
      (flatFppfModuleLowerShriek.singleDerived X H) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
