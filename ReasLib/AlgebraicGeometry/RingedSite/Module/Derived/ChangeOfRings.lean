/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Model
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived change of rings on a fixed site

A morphism of commutative structure sheaves determines extension of scalars on module sheaves.
This file exposes its canonical total left derived functor without requiring downstream files to
rebuild adjoint or derived-functor instances.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u v w z uX vX uY vY

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- An explicit model for derived module pullback along a ringed-site morphism.

The model carries the derived functor and its localization counit as concrete data. Unlike
`modulePullbackDerived`, it does not choose a functor from the proposition
`HasLeftDerivedFunctor`; downstream constructions can therefore keep a specified model stable. -/
@[stacks 05SA "explicit ringed-site derived pullback model"]
abbrev PullbackModel (f : Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [((f.modulePushforward.{z}).IsRightAdjoint)] :=
  CategoryTheory.Functor.LeftDerived.Model
      (modulePullbackToDerived.{z} f)
      (moduleLocalization.{z} Y)
      (ModuleQis.{z} Y)

section Model

variable {f : Hom X Y}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [((f.modulePushforward.{z}).IsRightAdjoint)]

/-- The concrete derived pullback functor carried by an explicit model. -/
@[stacks 05SA "derived pullback functor from an explicit model"]
noncomputable abbrev pullbackOfModel (M : PullbackModel f) :
    ModuleDerived.{z} Y ⥤ ModuleDerived.{z} X :=
  M.functor

/-- The localization counit carried by an explicit derived pullback model. -/
@[stacks 05SA "derived pullback model counit"]
abbrev pullbackOfModel_counit (M : PullbackModel f) :=
  M.counit

/-- The universal-property witness carried by an explicit derived pullback model. -/
@[stacks 05SA "derived pullback model universal property"]
abbrev pullbackOfModel_isLeftDerived (M : PullbackModel f) :=
  M.isLeftDerived

end Model

end RingedSite.Hom

namespace RingedSite.SameSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, z}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable {O O' : Sheaf J RingCat.{w}}

/-- The explicit derived pullback model for a same-site ring-sheaf map. -/
@[stacks 05SA "same-site explicit derived pullback model"]
abbrev PullbackModel (α : O ⟶ O')
    [((hom α).modulePushforward.{z}).IsRightAdjoint] :=
  RingedSite.Hom.PullbackModel (f := hom α)

/-- The concrete derived pullback functor selected by a same-site explicit model. -/
@[stacks 05SA "same-site derived pullback from an explicit model"]
noncomputable abbrev pullbackOfModel {α : O ⟶ O'}
    [((hom α).modulePushforward.{z}).IsRightAdjoint] (M : PullbackModel α) :=
  RingedSite.Hom.pullbackOfModel M

/-- The source-level extension of scalars along `α` admits a total left-derived functor.  This is an
existence gate; use `PullbackModel` when downstream data must retain a specified model. -/
@[stacks 06YY "existence of same-site derived extension of arbitrary rings"]
abbrev HasPullbackDerived (α : O ⟶ O')
    [((hom α).modulePushforward.{z}).IsRightAdjoint] : Prop :=
  Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{z} (hom α))
    (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf J O))

/-- Same-site restriction of scalars for arbitrary ring sheaves is the canonical right adjoint
of module pullback. -/
@[stacks 06YY "same-site restriction of arbitrary rings is right adjoint"]
instance modulePushforwardIsRightAdjoint (α : O ⟶ O') :
    ((hom α).modulePushforward.{z}).IsRightAdjoint := sorry

/-- Same-site extension of scalars for arbitrary ring sheaves admits its unbounded total left
derived functor. -/
@[stacks 06YY "same-site derived change of arbitrary rings"]
theorem modulePullbackToDerived_hasLeftDerived (α : O ⟶ O') :
    HasPullbackDerived.{u, v, w, z} α := sorry

/-- Typeclass owner for total derived same-site extension of scalars for ring sheaves. -/
@[stacks 06YY "same-site arbitrary-ring pullback has a left derived functor"]
instance modulePullbackToDerivedHasLeftDerived (α : O ⟶ O') :
    HasPullbackDerived.{u, v, w, z} α :=
  modulePullbackToDerived_hasLeftDerived α

/-- The canonical unbounded derived extension of scalars along a morphism of ring sheaves. -/
@[stacks 06YY "same-site derived extension of arbitrary rings"]
noncomputable abbrev pullbackDerived (α : O ⟶ O')
    [((hom α).modulePushforward.{z}).IsRightAdjoint]
    [HasPullbackDerived.{u, v, w, z} α] :
    RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf J O) ⥤
      RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf J O') :=
  RingedSite.Hom.modulePullbackDerived.{z} (hom α)

end RingedSite.SameSite

namespace SheafOfModules.RingedSite.SameSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, z}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable {O O' : Sheaf J CommRingCat.{w}}

/-- The explicit derived pullback model for a same-site commutative ring-sheaf map. -/
@[stacks 05SA "commutative same-site explicit derived pullback model"]
abbrev PullbackModel (α : O ⟶ O')
    [((sameSiteHom α).modulePushforward.{z}).IsRightAdjoint] :=
  RingedSite.Hom.PullbackModel (f := sameSiteHom α)

/-- The concrete derived pullback functor selected by a commutative explicit model. -/
@[stacks 05SA "commutative same-site derived pullback from an explicit model"]
noncomputable abbrev pullbackOfModel {α : O ⟶ O'}
    [((sameSiteHom α).modulePushforward.{z}).IsRightAdjoint] (M : PullbackModel α) :=
  RingedSite.Hom.pullbackOfModel M

/-- The commutative same-site pullback admits a selected total left-derived model. -/
@[stacks 06YY "existence of same-site commutative derived extension"]
abbrev HasPullbackDerived (α : O ⟶ O')
    [((sameSiteHom α).modulePushforward.{z}).IsRightAdjoint] : Prop :=
  Functor.HasLeftDerivedFunctor
    (RingedSite.Hom.modulePullbackToDerived.{z} (sameSiteHom α))
    (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofCommRingSheaf J O))

/-- Same-site restriction of scalars is the canonical right adjoint of module pullback. -/
@[stacks 06YY "same-site commutative restriction is right adjoint"]
instance modulePushforwardIsRightAdjoint (α : O ⟶ O') :
    ((sameSiteHom α).modulePushforward.{z}).IsRightAdjoint := sorry

/-- Same-site extension of scalars admits its canonical unbounded total left derived functor. -/
@[stacks 06YY "same-site change of rings"]
theorem modulePullbackToDerived_hasLeftDerived (α : O ⟶ O') :
    HasPullbackDerived.{u, v, w, z} α := sorry

/-- Typeclass owner for the total left derived same-site extension-of-scalars functor. -/
@[stacks 06YY "same-site commutative pullback has a left derived functor"]
instance modulePullbackToDerivedHasLeftDerived (α : O ⟶ O') :
    HasPullbackDerived.{u, v, w, z} α :=
  modulePullbackToDerived_hasLeftDerived α

/-- The canonical unbounded derived extension of scalars along `α : O ⟶ O'`. -/
@[stacks 06YY "same-site derived extension of scalars"]
noncomputable abbrev pullbackDerived (α : O ⟶ O')
    [((sameSiteHom α).modulePushforward.{z}).IsRightAdjoint]
    [HasPullbackDerived.{u, v, w, z} α] :
    RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O) ⥤
      RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O') :=
  RingedSite.Hom.modulePullbackDerived.{z} (sameSiteHom α)

end SheafOfModules.RingedSite.SameSite
