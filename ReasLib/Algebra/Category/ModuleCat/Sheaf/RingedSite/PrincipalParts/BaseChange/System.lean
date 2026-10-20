module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.BaseChange.Truncation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.OrderSystem

/-!
# Base change of the principal-parts order system

The base-change morphisms at all finite orders assemble into a morphism of sequential inverse
systems.  This is the bundled form of their compatibility with truncation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
variable (sq : CommSq a phi phi' b)
variable {F : ringedSiteModuleCategory J O₂}
variable {F' : ringedSiteModuleCategory J O₂'}
variable (alpha : F ⟶ (restrictionAlong b).obj F')

/-- Naturality of the all-order base-change map with respect to an arbitrary order transition. -/
theorem systemMap_naturality {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (PrincipalParts.system phi F).map f ≫ map sq alpha l.unop =
      map sq alpha k.unop ≫
        (PrincipalParts.system phi' F' ⋙ restrictionAlong b).map f := sorry

/-- Tag 0G3W: the morphism of all-order principal-parts systems induced by a commutative ring
square and a compatible module-sheaf morphism. -/
@[stacks 0G3W "base change of the principal-parts order system"]
noncomputable def systemMap (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    PrincipalParts.system phi F ⟶
      PrincipalParts.system phi' F' ⋙ restrictionAlong b where
  app k := map sq alpha k.unop
  naturality {_ _} f := systemMap_naturality sq alpha f

/-- Base change of all-order principal-parts systems preserves composition of ring squares and
compatible module-sheaf morphisms. -/
@[simp]
theorem systemMap_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq' : CommSq a' phi' phi'' b')
    {F'' : ringedSiteModuleCategory J O₂''}
    (alpha' : F' ⟶ (restrictionAlong b').obj F'') :
    systemMap (CommSq.horiz_comp sq sq')
        (alpha ≫ (restrictionAlong b).map alpha') =
      systemMap sq alpha ≫
        Functor.whiskerRight (systemMap sq' alpha') (restrictionAlong b) := sorry

end SheafOfModules.RingedSite.PrincipalParts.BaseChange
