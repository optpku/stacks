module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction
public import ReasLib.RingTheory.Pullback.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre-product adjunctions for surjective ring pullbacks

For the canonical square `B' = B ×_A A'` with `A' → A` surjective, the counit of the
fibre-product module adjunction is invertible, while each component of its unit is surjective.

@stack 07RU
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Pullback

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/-- For a surjective ring-pullback square, the counit of the fibre-product module adjunction is
an isomorphism. -/
@[stacks 07RU "surjective pullback counit"]
theorem counit_isIso (S : SurjectiveRingPullbackSituation B A A') :
    IsIso ((adjunction S.bprimeToB S.bprimeToAprime S.comm).counit) := sorry

/-- Every component of the unit for a surjective ring-pullback square is surjective on the
underlying module. -/
@[stacks 08IG "surjective pullback unit component"]
theorem unit_app_surjective (S : SurjectiveRingPullbackSituation B A A')
    (L : ModuleCat S.Bprime) :
    Function.Surjective
      (((adjunction S.bprimeToB S.bprimeToAprime S.comm).unit.app L).hom) := sorry

/-- The unit of the fibre-product module adjunction need not be injective, even for a
surjective ring-pullback square. -/
@[stacks 08IG "surjective pullback unit need not be injective"]
theorem unit_app_not_injective_in_general :
    ¬ ∀ {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
        (S : SurjectiveRingPullbackSituation B A A') (L : ModuleCat S.Bprime),
        Function.Injective
          (((adjunction S.bprimeToB S.bprimeToAprime S.comm).unit.app L).hom) := sorry

/-- A morphism of pullback-module triples that is surjective on both components induces a
surjective morphism of fibre-product modules. -/
@[stacks 08KJ "surjectivity on fibre-product modules"]
theorem map_surjective (S : SurjectiveRingPullbackSituation B A A')
    {X Y : Pullback.Category S.toA S.fromAprime} (f : X ⟶ Y)
    (hfst : Function.Surjective f.fst) (hsnd : Function.Surjective f.snd) :
    Function.Surjective ((rightAdjoint S.bprimeToB S.bprimeToAprime S.comm).map f) := sorry

end CategoryTheory.ModuleCat.Pullback
