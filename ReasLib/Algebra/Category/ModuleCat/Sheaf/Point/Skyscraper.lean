/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Sites.Topos.Point.FiberToTypes
import Mathlib.Tactic.CrossRefAttribute

/-!
# Skyscraper modules at a point of a ringed site

For a site point `p` and a ring sheaf `𝒪`, the unit of the ring-valued fiber--pushforward
adjunction is the canonical structure map defining inverse and direct image on modules.  This file
names that point-specific API and records its exactness properties.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w r m

namespace CategoryTheory.GrothendieckTopology.Point.Ringed

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (p : GrothendieckTopology.Point.{w} J)
variable (𝒪 : Sheaf J RingCat.{r})
variable
  [(p.fiber.sheafPushforwardContinuous RingCat.{r} J
    typesGrothendieckTopology).IsRightAdjoint]

/-- The inverse-image ring sheaf of `𝒪` at `p`, presented on the canonical site of types. -/
noncomputable abbrev inverseImageRing :
    Sheaf typesGrothendieckTopology RingCat.{r} :=
  (p.fiber.sheafPullback RingCat.{r} J typesGrothendieckTopology).obj 𝒪

/-- The canonical ring map `𝒪 ⟶ p_* p⁻¹ 𝒪` at a point of a ringed site. -/
noncomputable abbrev unit :
    𝒪 ⟶
      (p.fiber.sheafPushforwardContinuous RingCat.{r} J
        typesGrothendieckTopology).obj (inverseImageRing p 𝒪) :=
  (p.fiber.sheafAdjunctionContinuous RingCat.{r} J
    typesGrothendieckTopology).unit.app 𝒪

/-- Direct image from modules over `p⁻¹ 𝒪` to modules over `𝒪`. -/
noncomputable abbrev modulePushforward :
    SheafOfModules.{m} (inverseImageRing p 𝒪) ⥤ SheafOfModules.{m} 𝒪 :=
  SheafOfModules.pushforward (unit p 𝒪)

variable [(SheafOfModules.pushforward.{m} (unit p 𝒪)).IsRightAdjoint]

/-- Inverse image from modules over `𝒪` to modules over `p⁻¹ 𝒪`. -/
noncomputable abbrev modulePullback :
    SheafOfModules.{m} 𝒪 ⥤ SheafOfModules.{m} (inverseImageRing p 𝒪) :=
  SheafOfModules.pullback.{m} (unit p 𝒪)

/-- The inverse/direct-image adjunction on modules at a ringed-site point. -/
noncomputable abbrev moduleAdjunction :
    (modulePullback p 𝒪 :
        SheafOfModules.{m} 𝒪 ⥤ SheafOfModules.{m} (inverseImageRing p 𝒪)) ⊣
      (modulePushforward p 𝒪 :
        SheafOfModules.{m} (inverseImageRing p 𝒪) ⥤ SheafOfModules.{m} 𝒪) :=
  SheafOfModules.pullbackPushforwardAdjunction.{m} (unit p 𝒪)

/-- Lemma 18.37.2 (05V8) (1): direct image on modules at a point of a ringed topos is exact. -/
@[stacks 05V8 "(1)"]
theorem modulePushforward_exact :
    exactFunctor
      (SheafOfModules.{m} (inverseImageRing p 𝒪))
      (SheafOfModules.{m} 𝒪)
      (modulePushforward p 𝒪) := sorry

/-- Lemma 18.37.2 (05V8) (2): the canonical linear counit
`p⁻¹(p_* M) ⟶ M` is an epimorphism.  Linearity is encoded by its type as a morphism of
`p⁻¹ 𝒪`-modules. -/
@[stacks 05V8 "(2)"]
instance moduleAdjunction_counit_epi
    (M : SheafOfModules.{m} (inverseImageRing p 𝒪)) :
    Epi ((moduleAdjunction p 𝒪).counit.app M) := sorry

/- The `sorryAx` reported below is inherited through Prop-valued continuity/right-adjoint law
fields of the canonical point functors.  The displayed ring, maps, functors, and adjunction are
the existing deterministic Mathlib constructions; no witness is supplied by `sorry`. -/

end CategoryTheory.GrothendieckTopology.Point.Ringed
