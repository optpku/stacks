module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_7_8_ClosedSupport

/-!
# Derived pushforward of bounded coherent complexes with proper support

Along a locally of finite type morphism of algebraic spaces with Noetherian
target, derived pushforward preserves bounded coherent cohomology when every
cohomology sheaf has support proper over the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 75.8.1: if `f : X ⟶ Y` is a locally of finite type morphism of algebraic
spaces over a scheme `S` with `Y` Noetherian, and `E` is an object of
`D^b_Coh(𝒪_X)` such that the support of `H^i(E)` is proper over `Y` for all `i`,
then `(Modules.pushforwardDerived f).obj E` is an object of `D^b_Coh(𝒪_Y)`. -/
@[stacks 08GK]
theorem pushforwardDerived_boundedCoherent_of_properSupport
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf Y))
        ((Modules.pushforwardDerived f).obj E) ∧
      (t.bounded : ObjectProperty (ModuleDerived Y))
        ((Modules.pushforwardDerived f).obj E) := sorry

/-- Derived pushforward of a bounded coherent complex with cohomology support
proper over a Noetherian target has coherent cohomology. -/
theorem pushforwardDerived_cohomologyIn_of_properSupport
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf Y))
      ((Modules.pushforwardDerived f).obj E) := sorry

/-- Derived pushforward of a bounded coherent complex with cohomology support
proper over a Noetherian target is cohomologically bounded. -/
theorem pushforwardDerived_bounded_of_properSupport
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) :
    (t.bounded : ObjectProperty (ModuleDerived Y))
      ((Modules.pushforwardDerived f).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
