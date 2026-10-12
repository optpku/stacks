/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# The chaotic Grothendieck topology

The bottom Grothendieck topology is the chaotic topology: every presheaf is a sheaf.  This file
records the resulting canonical instances so that constructions on presheaves can be reused on
chaotic sites without rebuilding local topology data at each call site.

@stack 08PF
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uC vC uA vA uB vB w

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace Functor

/-- Every functor between chaotic sites is continuous. -/
instance isContinuous_bot {D : Type uA} [Category.{vA} D] (F : C ⥤ D) :
    F.IsContinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) := sorry

/-- Every functor between chaotic sites is cocontinuous. -/
instance isCocontinuous_bot {D : Type uA} [Category.{vA} D] (F : C ⥤ D) :
    F.IsCocontinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) := sorry

end Functor

namespace GrothendieckTopology

/-- Composition by any functor preserves sheaves for the chaotic topology. -/
instance hasSheafCompose_bot {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] (F : A ⥤ B) :
    (⊥ : GrothendieckTopology C).HasSheafCompose F := sorry

/-- Every functor preserves sheafification for the chaotic topology. -/
@[stacks 08PF "chaotic sheafification preservation"]
instance preservesSheafification_bot {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] (F : A ⥤ B) :
    (⊥ : GrothendieckTopology C).PreservesSheafification F := sorry

/-- On a chaotic site, weak equivalences of additive-commutative-group-valued presheaves are
exactly the locally bijective morphisms. -/
@[stacks 08PF "chaotic additive-presheaf local-bijection owner"]
instance wEqualsLocallyBijective_bot :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{w} := sorry

/-- On the chaotic topology, locally bijective morphisms of ring presheaves are exactly
objectwise bijective morphisms.  This supplies the constant-ring sheaf presentation used by
module-valued presheaves. -/
@[stacks 08PF "chaotic ring-presheaf local-bijection owner"]
instance wEqualsLocallyBijective_bot_ring :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective RingCat.{w} := sorry

end GrothendieckTopology

/-- On the bottom topology, every sheaf is already its underlying presheaf. -/
@[stacks 08PF "chaotic sheaf-to-presheaf equivalence"]
instance sheafToPresheaf_bot_isEquivalence {A : Type uA} [Category.{vA} A] :
    (sheafToPresheaf (⊥ : GrothendieckTopology C) A).IsEquivalence :=
  (sheafBotEquivalence A).isEquivalence_functor

/-- The chaotic sheaf-to-presheaf equivalence preserves finite limits. -/
@[stacks 08PF "chaotic sheaf-to-presheaf finite limits"]
instance sheafToPresheaf_bot_preservesFiniteLimits
    {A : Type uA} [Category.{vA} A] :
    PreservesFiniteLimits (sheafToPresheaf (⊥ : GrothendieckTopology C) A) := sorry

/-- The chaotic sheaf-to-presheaf equivalence preserves finite colimits. -/
@[stacks 08PF "chaotic sheaf-to-presheaf finite colimits"]
instance sheafToPresheaf_bot_preservesFiniteColimits
    {A : Type uA} [Category.{vA} A] :
    PreservesFiniteColimits (sheafToPresheaf (⊥ : GrothendieckTopology C) A) := sorry

end CategoryTheory
