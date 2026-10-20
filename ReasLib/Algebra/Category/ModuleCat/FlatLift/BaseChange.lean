module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Localization.Away.Relative
public import ReasLib.RingTheory.RingHom.Quotient
public import ReasLib.Algebra.Homology.DerivedCategory.NilpotentLift

/-!
# Flat lifts after inverting an element, and comparison along cartesian squares

Principal localization gives a local relative-flat liftability condition.
For cartesian diagrams of nilpotent ring quotients, this condition compares
relative-flat liftability before and after extending scalars.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.NilpotentLift

/-- Existence of an `A'`-flat `Localization.Away g`-module lifting
`(ModuleCat.extendScalars (algebraMap P (Localization.Away (algebraMap P' P g)))).obj M`. -/
noncomputable def existsFlatLift_away (A' P' : Type u) {P : Type u}
    [CommRing A'] [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (g : P') (M : ModuleCat.{u} P) : Prop :=
  -- Local instance justification (instance diamond): Relative.algebraMapAlgebra is deliberately non-global because a map-induced Localization.Away action can conflict with a native action when source and target coincide.
  letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
    Localization.Away.Relative.algebraMapAlgebra g
  existsFlatLift A' (Localization.Away g)
    ((ModuleCat.extendScalars (algebraMap P (Localization.Away (algebraMap P' P g)))).obj M)

/-- Unfolding of `existsFlatLift_away` to `existsFlatLift` after inverting `g`. -/
theorem existsFlatLift_away_iff (A' P' : Type u) {P : Type u}
    [CommRing A'] [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (g : P') (M : ModuleCat.{u} P) :
    existsFlatLift_away A' P' g M ↔
      -- Local instance justification (instance diamond): Relative.algebraMapAlgebra is deliberately non-global because a map-induced Localization.Away action can conflict with a native action when source and target coincide.
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        Localization.Away.Relative.algebraMapAlgebra g
      existsFlatLift A' (Localization.Away g)
        ((ModuleCat.extendScalars (algebraMap P (Localization.Away (algebraMap P' P g)))).obj M) :=
  Iff.rfl

/-- If the Noetherian squares `A' → P'` over `A → P` and `P' → Q'` over `P → Q` are cartesian,
the horizontal maps are flat, the vertical maps are surjective with nilpotent
kernels, `P' ⧸ J' ≃ Q' ⧸ J' Q'`, and `M` is an `A`-flat `P`-module whose
localizations `M_g` admit `A'`-flat `(P')_g`-lifts for every `g ∈ J'`, then `M`
has an `A'`-flat `P'`-lift if and only if `M ⊗[P] Q` has an `A'`-flat `Q'`-lift. -/
theorem existsFlatLift_iff_existsFlatLift_extendScalars
    {A' A P' P Q' Q : Type u}
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q']
    [Algebra A P] [Algebra P' P] [Algebra P' Q'] [Algebra P Q] [Algebra Q' Q]
    [Algebra A' P] [Algebra P' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower P' P Q] [IsScalarTower P' Q' Q]
    (hcartAP : CategoryTheory.IsPullback
      (CommRingCat.ofHom (algebraMap A' P')) (CommRingCat.ofHom (algebraMap A' A))
      (CommRingCat.ofHom (algebraMap P' P)) (CommRingCat.ofHom (algebraMap A P)))
    (hcartPQ : CategoryTheory.IsPullback
      (CommRingCat.ofHom (algebraMap P' Q')) (CommRingCat.ofHom (algebraMap P' P))
      (CommRingCat.ofHom (algebraMap Q' Q)) (CommRingCat.ofHom (algebraMap P Q)))
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P']
    [IsNoetherianRing P] [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Module.Flat A' P'] [Module.Flat P' Q'] [Module.Flat A P] [Module.Flat P Q]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hkerA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : IsNilpotent (RingHom.ker (algebraMap P' P)))
    (hsurjQ : Function.Surjective (algebraMap Q' Q))
    (hkerQ : IsNilpotent (RingHom.ker (algebraMap Q' Q)))
    (J' : Ideal P')
    (hJ : Function.Bijective ((algebraMap P' Q').quotientByIdeal J'))
    (M : ModuleCat.{u} P)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P)).obj M))
    (hloc : ∀ g ∈ J', existsFlatLift_away A' P' g M) :
    existsFlatLift A' P' M ↔
      existsFlatLift A' Q' ((ModuleCat.extendScalars (algebraMap P Q)).obj M) :=
  sorry

end CategoryTheory.ModuleCat.NilpotentLift

end
