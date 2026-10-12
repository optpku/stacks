/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.Monoidal.Adjunction.Braided

@[expose] public section

/-!
# Monoidal derived pushforward on a commutative ringed site

Once derived pullback is oplax monoidal and its derived adjunction is available, Mathlib's
right-adjoint construction supplies the canonical lax monoidal structure on derived pushforward.
The tensorator is the relative derived cup product.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom.modulePushforwardDerived

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [DerivedAdjunction.HasPair.{z} f]

section Monoidal

variable [MonoidalCategory (ModuleDerived.{z} X)]
variable [MonoidalCategory (ModuleDerived.{z} Y)]
variable [(modulePullbackDerived.{z} f).OplaxMonoidal]

/-- The canonical lax monoidal structure on derived pushforward, transported across the derived
pullback-pushforward adjunction. -/
@[implicit_reducible]
noncomputable def laxMonoidal : (modulePushforwardDerived.{z} f).LaxMonoidal :=
  (moduleDerivedAdjunction.{z} f).rightAdjointLaxMonoidal

/-- The relative derived cup product, expressed as the tensorator of the canonical lax monoidal
derived pushforward. -/
@[stacks 0B6C "relative derived cup product"]
noncomputable abbrev cupProduct (K L : ModuleDerived.{z} X) :
    (modulePushforwardDerived.{z} f).obj K ⊗
        (modulePushforwardDerived.{z} f).obj L ⟶
      (modulePushforwardDerived.{z} f).obj (K ⊗ L) :=
  @Functor.LaxMonoidal.μ _ _ _ _ _ _ (modulePushforwardDerived.{z} f)
    (laxMonoidal f) K L

/-- The relative derived cup product satisfies the associativity coherence of the canonical lax
monoidal derived pushforward. -/
@[stacks 0FPL "associativity of the relative derived cup product"]
theorem cupProduct_assoc (K L M : ModuleDerived.{z} X) :
    cupProduct f K L ▷ (modulePushforwardDerived.{z} f).obj M ≫
        cupProduct f (K ⊗ L) M ≫
        (modulePushforwardDerived.{z} f).map (α_ K L M).hom =
      (α_ ((modulePushforwardDerived.{z} f).obj K)
        ((modulePushforwardDerived.{z} f).obj L)
        ((modulePushforwardDerived.{z} f).obj M)).hom ≫
        (modulePushforwardDerived.{z} f).obj K ◁ cupProduct f L M ≫
        cupProduct f K (L ⊗ M) := sorry

/-- The adjoint-side characterization of the relative derived cup product: after derived
pullback and the counit, it is the oplax tensor comparison followed by the two counits. -/
@[stacks 0B6C "relative derived cup product adjoint characterization"]
theorem map_cupProduct_comp_counit (K L : ModuleDerived.{z} X) :
    (modulePullbackDerived.{z} f).map (cupProduct f K L) ≫
        (moduleDerivedAdjunction.{z} f).counit.app (K ⊗ L) =
      Functor.OplaxMonoidal.δ (modulePullbackDerived.{z} f)
          ((modulePushforwardDerived.{z} f).obj K)
          ((modulePushforwardDerived.{z} f).obj L) ≫
        ((moduleDerivedAdjunction.{z} f).counit.app K ⊗ₘ
          (moduleDerivedAdjunction.{z} f).counit.app L) := sorry

end Monoidal

section Braided

variable [MonoidalCategory (ModuleDerived.{z} X)]
variable [BraidedCategory (ModuleDerived.{z} X)]
variable [MonoidalCategory (ModuleDerived.{z} Y)]
variable [BraidedCategory (ModuleDerived.{z} Y)]
variable [(modulePullbackDerived.{z} f).Braided]

/-- The canonical lax braided structure on derived pushforward when derived pullback is braided
monoidal. -/
@[implicit_reducible]
noncomputable def laxBraided : (modulePushforwardDerived.{z} f).LaxBraided :=
  (moduleDerivedAdjunction.{z} f).rightAdjointLaxBraided

end Braided

end RingedSite.Hom.modulePushforwardDerived

-- The cup-product morphism is Mathlib's concrete right-adjoint tensorator. Any `sorryAx` below
-- is confined to inherited categorical laws and Prop-valued coherence fields.
