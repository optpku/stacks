/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect complexes and dualizability on commutative ringed sites

For the canonical K-flat tensor product on the derived category of modules over a commutative
ring sheaf, a perfect object is right-dualizable.  Perfectness remains an object property; it is
not installed as a typeclass merely to synthesize duality data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

set_option checkBinderAnnotations false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  HasWeakSheafify
    ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [KFlat.HomotopyTensorDescends O] [KFlat.TensorDescends O]
variable [KFlat.IsLocalization O]

/-- A perfect derived module over a commutative ring sheaf is right-dualizable for the canonical
K-flat derived tensor product. -/
@[stacks 0944 "perfect implies right-dualizable"]
theorem IsPerfect.isRightDualizable
    {K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : IsPerfect K) :
    IsRightDualizable K := sorry

end RingedSite.Hom.ModuleDerived
