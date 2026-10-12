/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Colimits and the module universe-lift functor

The universe-lift functor on modules preserves arbitrary colimits. Its compatibility with the
corresponding lift on additive commutative groups is exposed as a natural isomorphism, so clients
can transport concrete colimit witnesses without rebuilding the comparison.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe w' w v' v u

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace uliftFunctor

/-- The universe-lift functor on modules preserves colimits of arbitrary size. -/
noncomputable instance preservesColimitsOfSize :
    PreservesColimitsOfSize.{w', w} (ModuleCat.uliftFunctor.{v', v} R) := sorry

namespace forget₂Iso

/-- Naturality of the comparison between forgetting a lifted module and lifting its underlying
additive commutative group. -/
theorem naturality
    {X Y : ModuleCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙
        AddCommGrpCat.uliftFunctor.{v', v}).map f ≫ 𝟙 _ =
      𝟙 _ ≫
        (uliftFunctor.{v', v} R ⋙
          forget₂ (ModuleCat.{max v v'} R) AddCommGrpCat.{max v v'}).map f := sorry

end forget₂Iso

/-- Forgetting a lifted module to additive commutative groups agrees naturally with lifting the
underlying additive commutative group. -/
noncomputable def forget₂Iso :
    forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙
        AddCommGrpCat.uliftFunctor.{v', v} ≅
      ModuleCat.uliftFunctor.{v', v} R ⋙
        forget₂ (ModuleCat.{max v v'} R) AddCommGrpCat.{max v v'} :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => forget₂Iso.naturality (R := R) f)

namespace forget₂Iso

/-- The forward component of `uliftFunctor.forget₂Iso` is the identity. -/
@[simp]
theorem hom_app (X : ModuleCat.{v} R) :
    (uliftFunctor.forget₂Iso.{v', v} R).hom.app X = 𝟙 _ := sorry

/-- The inverse component of `uliftFunctor.forget₂Iso` is the identity. -/
@[simp]
theorem inv_app (X : ModuleCat.{v} R) :
    (uliftFunctor.forget₂Iso.{v', v} R).inv.app X = 𝟙 _ := sorry

end forget₂Iso

end uliftFunctor

end ModuleCat
