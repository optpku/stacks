module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Derived pushforward of bounded and bounded-below coherent complexes with proper support

Along a locally of finite type morphism of algebraic spaces with Noetherian
target, derived pushforward preserves bounded coherent cohomology when every
cohomology sheaf has support proper over the target. It preserves bounded-below
coherent cohomology when every cohomology sheaf has support proper over the base scheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Along a locally of finite type morphism of algebraic spaces with Noetherian
target, the derived pushforward of a bounded complex with coherent cohomology
and degreewise support proper over the target is bounded with coherent cohomology. -/
@[stacks 08GK]
theorem pushforwardDerived_boundedCoherent_of_properSupport
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf Y))
        ((Modules.moduleDerivedPushforward f).obj E) ∧
      (t.bounded : ObjectProperty (ModuleDerived Y))
        ((Modules.moduleDerivedPushforward f).obj E) := sorry

/-- Along a locally of finite type morphism of algebraic spaces over a scheme `S`
with Noetherian target, the derived pushforward of a bounded-below complex with
coherent cohomology and degreewise support proper over `S` is bounded below with
coherent cohomology. -/
@[stacks 0D0R]
theorem pushforwardDerived_boundedBelowCoherent_of_properSupport
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
    (E : ModuleDerived X)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) E)
    (hE_plus : (t.plus : ObjectProperty (ModuleDerived X)) E)
    (hE_support : ∀ i : ℤ, ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (Modules.closedSupport
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf Y))
        ((Modules.moduleDerivedPushforward f).obj E) ∧
      (t.plus : ObjectProperty (ModuleDerived Y))
        ((Modules.moduleDerivedPushforward f).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
