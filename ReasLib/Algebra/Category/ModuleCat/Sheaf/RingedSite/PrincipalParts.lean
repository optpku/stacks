/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator

/-!
# Principal parts on a ringed site

For a morphism of commutative ring sheaves `φ : O₁ ⟶ O₂`, an `O₂`-module sheaf `F`, and
an order bound `k`, the ringed-site differential-operator module owns the additive functor of
operators out of `F` and its underlying Type-valued functor.  This file develops the universal
property of a corepresenting principal-parts sheaf.

The declarations here are presentation-independent: given any corepresenting object, they expose
its universal operator, classifier, factorization, and uniqueness API.  The canonical sheafified
model and the resulting existence theorem live in the downstream `PrincipalParts.Construction`
owner, where their actual sheafification assumptions are visible.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

namespace PrincipalParts

/-- The universal order-`k` differential operator attached to a fixed corepresenting
principal-parts sheaf. -/
def universalOperator
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj P :=
  DifferentialOperators.toHom (hP.homEquiv (𝟙 P))

/-- The universal operator attached to a fixed corepresentation has order at most `k`. -/
theorem universalOperator_mem
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P) :
    IsDifferentialOperatorOfOrder φ (universalOperator hP) k := sorry

/-- Under a fixed corepresenting equivalence, a morphism out of the principal-parts sheaf is
sent to postcomposition of the universal differential operator by that morphism. -/
theorem homEquiv_apply
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P) (α : P ⟶ G) :
    DifferentialOperators.toHom (hP.homEquiv α) =
      universalOperator hP ≫ (restrictionAlong φ).map α := sorry

/-- The morphism out of a fixed corepresenting principal-parts sheaf classified by an
order-`k` differential operator. -/
def desc
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) : P ⟶ G :=
  hP.homEquiv.symm (DifferentialOperators.ofHom D hD)

/-- The morphism classified by a differential operator factors that operator through the
universal principal-parts operator. -/
theorem desc_fac
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    universalOperator hP ≫ (restrictionAlong φ).map (desc hP D hD) = D := sorry

/-- A morphism out of a fixed corepresenting principal-parts sheaf is determined by its
factorization of an order-bounded differential operator. -/
theorem desc_unique
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) (α : P ⟶ G)
    (hα : universalOperator hP ≫ (restrictionAlong φ).map α = D) :
    α = desc hP D hD := sorry

/-- A fixed corepresenting principal-parts sheaf represents order-`k` differential operators by
unique `O₂`-linear morphisms out of it. -/
theorem representsDifferentialOperators
    {φ : O₁ ⟶ O₂} {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {P : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (hP : (DifferentialOperators.functor φ F k).CorepresentableBy P)
    (G : ringedSiteModuleCategory.{u, v, z, w} J O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    ∃! α : P ⟶ G,
      universalOperator hP ≫ (restrictionAlong φ).map α = D := sorry

end PrincipalParts

end SheafOfModules.RingedSite
