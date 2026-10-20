module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.QuotientStack.AbstractGroup
public import ReasLib.AlgebraicGeometry.QuotientStack.ConstantGroup

/-!
# Quotients by abstract group actions

The common universe of the group and the base scheme supplies the size restriction
needed to represent the constant sheaf by the coproduct group scheme.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Remark 95.15.5. The abstract-group quotient is equivalent over the fppf base
to the quotient by its induced constant-group-scheme action. -/
@[stacks 0371] #check
  (AlgebraicGeometry.QuotientStack.BaseChange.equivalent_baseChange :
    ∀ {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}
      (ρ : G →* Aut X),
      AlgebraicGeometry.QuotientStack.AbstractGroup.stack ρ ≌
        AlgebraicGeometry.QuotientStack.BaseChange.stack ρ)

#check (AlgebraicGeometry.QuotientStack.AbstractGroup.stack :
  ∀ {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}
    (_ρ : G →* Aut X), StackOver.Groupoids (Scheme.fppfTopology.over S))

#check (AlgebraicGeometry.QuotientStack.AbstractGroup.stack_p :
  ∀ {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}
    (ρ : G →* Aut X),
    (AlgebraicGeometry.QuotientStack.AbstractGroup.stack ρ).p =
      AlgebraicGeometry.QuotientStack.AbstractGroup.forget ρ)

#check (AlgebraicGeometry.QuotientStack.BaseChange.constantSheaf_represented :
  ∀ (S : Scheme.{u}) (G : GrpCat.{u}),
    IsIsomorphic (AlgebraicGeometry.QuotientStack.AbstractGroup.constantGroupSheaf S G).obj
      (yonedaGrp.obj (ConstantGroup.baseChange S G)))

#check (AlgebraicGeometry.QuotientStack.BaseChange.equivalent_baseChange_isEquivalence :
  ∀ {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}
    (ρ : G →* Aut X),
    StackOver.Groupoids.Hom.IsEquivalence
      (AlgebraicGeometry.QuotientStack.BaseChange.equivalent_baseChange ρ).hom)
