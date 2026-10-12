/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor of modules on a commutative ringed site

The source-facing Tor object is homology of the genuine two-variable derived tensor bifunctor.
This avoids imposing projective resolutions on a category of module sheaves: the ringed-site
construction is instead backed by the K-flat derived-tensor model.
-/

@[expose] public section

-- Keep the existing standard derived-category model available in this leaf.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory ComplexShape

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable [KFlat.HomotopyTensorDescends O] [Tensor.Has O]

/-- Definition 21.17.14 (08FF): the two-variable Tor functor on derived module sheaves over a
commutative ringed site. -/
@[stacks 08FF "ringed-site Tor functor"]
noncomputable abbrev torFunctor (p : ℕ) :
    ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ×
        ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O) ⥤
      ModuleCat.{w} (RingedSite.ofCommRingSheaf J O) :=
  DerivedCategory.DerivedTensor.Bifunctor.torFunctor
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) p

/-- The `p`-th Tor object of arbitrary derived module sheaves over a commutative ringed site. -/
@[stacks 08FF "Tor of derived ringed-site modules"]
noncomputable abbrev torObj (p : ℕ)
    (K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf J O) :=
  (torFunctor O p).obj (K, L)

/-- The `p`-th Tor object of two module sheaves, defined as degree `-p` homology of their
two-variable derived tensor product. -/
@[stacks 08FF "Tor of two ringed-site modules"]
noncomputable abbrev tor (p : ℕ)
    (F G : ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf J O) :=
  DerivedCategory.DerivedTensor.Bifunctor.tor
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) p F G

-- Any `sorryAx` below is inherited from the Prop-valued derived-tensor existence and
-- naturality/coherence laws.  The Tor functor and its object views are explicit aliases of the
-- canonical two-variable derived-tensor homology owner.

end RingedSite.Hom.ModuleDerived

end
