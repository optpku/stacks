module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative differentials for morphisms of ringed spaces

This file specializes relative derivations and differentials to a morphism `f : X ⟶ S` of
ringed spaces.  It provides named API for the represented derivation functor and reserves
`Ω[f]` and `d[f]` as concise notation for its canonical owner objects.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open TopCat.Sheaf
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X S : RingedSpace.{u}}

/-- The type of `S`-derivations from `𝒪_X` to an `𝒪_X`-module `F`. -/
@[stacks 08RT "relative derivations"]
abbrev derivations (f : X ⟶ S) (F : X.Modules) : Type _ :=
  SheafOfModules.RelativeDerivation
    (J := Opens.grothendieckTopology X)
    (inverseImageStructureSheafHomComm f) F

/-- The sheaf of relative differentials `Ω_{X/S}` of a morphism of ringed spaces. -/
@[stacks 08RT "relative differentials"]
abbrev differentials (f : X ⟶ S) : X.Modules :=
  TopCat.Sheaf.relativeDifferentials
    (inverseImageStructureSheafHomComm f)

/-- The universal `S`-derivation `d_{X/S} : 𝒪_X ⟶ Ω_{X/S}`. -/
@[stacks 08RT "universal derivation"]
abbrev universalDerivation (f : X ⟶ S) :
    derivations f (differentials f) :=
  TopCat.Sheaf.relativeDifferential
    (inverseImageStructureSheafHomComm f)

/-- The morphism `Ω_{X/S} ⟶ F` represented by an `S`-derivation into `F`. -/
@[stacks 08RT "derivation descent"]
abbrev differentialDesc (f : X ⟶ S) {F : X.Modules}
    (D : derivations f F) : differentials f ⟶ F :=
  TopCat.Sheaf.relativeDifferentialDesc
    (inverseImageStructureSheafHomComm f) D

/-- The Type-valued functor of `S`-derivations with varying target module sheaf. -/
@[stacks 08RT "derivation functor"]
noncomputable abbrev derivationsFunctor (f : X ⟶ S) :
    X.Modules ⥤ Type _ :=
  SheafOfModules.RelativeDerivation.functor
    (J := Opens.grothendieckTopology X) (inverseImageStructureSheafHomComm f)

/-- Morphisms out of `Ω[f]` are equivalent to `S`-derivations with the same target. -/
@[stacks 08RT "morphism--derivation equivalence"]
noncomputable abbrev homEquiv (f : X ⟶ S) (F : X.Modules) :
    (differentials f ⟶ F) ≃ derivations f F :=
  TopCat.Sheaf.RelativeDifferentials.homEquiv
    (inverseImageStructureSheafHomComm f) F

/-- The sheaf `Ω[f]` corepresents the functor of `S`-derivations. -/
@[stacks 08RT "corepresented derivation functor"]
noncomputable abbrev corepresentableBy (f : X ⟶ S) :
    (derivationsFunctor f).CorepresentableBy (differentials f) :=
  TopCat.Sheaf.RelativeDifferentials.corepresentableBy
    (inverseImageStructureSheafHomComm f)

/-- The natural representing isomorphism for the `S`-derivation functor. -/
@[stacks 08RT "representing isomorphism"]
noncomputable abbrev representingIso (f : X ⟶ S) :
    coyoneda.obj (Opposite.op (differentials f)) ≅ derivationsFunctor f :=
  TopCat.Sheaf.RelativeDifferentials.representingIso
    (inverseImageStructureSheafHomComm f)

/-- Descending an `S`-derivation through `Ω_{X/S}` recovers the original derivation. -/
@[stacks 08RT "universal factorization"]
theorem differentialDesc_fac (f : X ⟶ S) {F : X.Modules}
    (D : derivations f F) :
    (universalDerivation f).postcomp (differentialDesc f D).val = D := sorry

/-- A morphism from `Ω_{X/S}` is determined by its composite with `d_{X/S}`. -/
theorem universalDerivation_postcomp_injective (f : X ⟶ S) {F : X.Modules}
    ⦃g h : differentials f ⟶ F⦄
    (eq : (universalDerivation f).postcomp g.val =
      (universalDerivation f).postcomp h.val) :
    g = h := sorry

/-- The sheaf `Ω_{X/S}` represents the functor of `S`-derivations. -/
@[stacks 08RT "universal property"]
theorem differentials_representsDerivations
    (f : X ⟶ S) (F : X.Modules) (D : derivations f F) :
    ∃! g : differentials f ⟶ F,
      (universalDerivation f).postcomp g.val = D := sorry

end AlgebraicGeometry.RingedSpace.Hom

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}

/-- `Ω[f]` is the sheaf of relative differentials `Ω_{X/S}` for a morphism of ringed spaces. -/
scoped[AlgebraicGeometry] notation3:max "Ω[" f "]" =>
  RingedSpace.Hom.differentials f

/-- `d[f]` is the universal derivation attached to a morphism of ringed spaces. -/
scoped[AlgebraicGeometry] notation3:max "d[" f "]" =>
  RingedSpace.Hom.universalDerivation f

end AlgebraicGeometry.RingedSpace
