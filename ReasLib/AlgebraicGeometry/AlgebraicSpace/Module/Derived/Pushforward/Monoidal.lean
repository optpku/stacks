module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # The derived module adjunction and monoidal pushforward

The module pullback–pushforward adjunction induces an adjunction on the unbounded
derived categories. A monoidal structure on derived pullback then determines a
lax monoidal structure on derived pushforward.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ModuleDerived

/-- The absolute-derived pair condition for module pullback and pushforward on
homotopy categories, localized at quasi-isomorphisms. -/
abbrev HasDerivedAdjunction {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  @Adjunction.TotalDerived.HasPair _ _ _ _ _ _ _ _
    ((Modules.pullback f).mapHomotopyCategory (up ℤ))
    ((Modules.pushforward f).mapHomotopyCategory (up ℤ))
    (HomotopyCategory.quasiIso Y.Modules (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance
    (instHasLeftDerivedFunctor_toDerived_pullback f)
    (inferInstanceAs
      ((Functor.Homotopy.toDerived (Modules.pushforward f)).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso X.Modules (up ℤ))))

/-- Derived module pullback is left adjoint to derived module pushforward,
via the canonical total-derived comparison for pullback. -/
def pullbackPushforwardAdjunction {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [HasDerivedAdjunction f] :
    pullback f ⊣ Modules.moduleDerivedPushforward f :=
  (@Adjunction.TotalDerived.HasPair.derived _ _ _ _ _ _ _ _
    ((Modules.pullback f).mapHomotopyCategory (up ℤ))
    ((Modules.pushforward f).mapHomotopyCategory (up ℤ))
    (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
    (HomotopyCategory.quasiIso Y.Modules (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance
    (instHasLeftDerivedFunctor_toDerived_pullback f)
    (inferInstanceAs
      ((Functor.Homotopy.toDerived (Modules.pushforward f)).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso X.Modules (up ℤ))))
    inferInstance).ofNatIsoLeft (pullbackIsoTotalLeftDerived f).symm

end ModuleDerived

/-- The lax monoidal structure on derived module pushforward induced by the
module-derived adjunction and the monoidal structure of derived pullback. -/
@[implicit_reducible]
def Modules.moduleDerivedPushforward.laxMonoidal
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [ModuleDerived.HasDerivedAdjunction f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [Functor.Monoidal (ModuleDerived.pullback f)] :
    Functor.LaxMonoidal (Modules.moduleDerivedPushforward f) :=
  (ModuleDerived.pullbackPushforwardAdjunction f).rightAdjointLaxMonoidal

end AlgebraicGeometry.AlgebraicSpace
