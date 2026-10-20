module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Morphisms.Thickening.FiniteOrder
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Morphism properties in finite-order deformations

This file records invariance of scheme-morphism properties in cartesian diagrams over a
finite-order thickening of the base, assuming that the ambient source is flat over the base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsFiniteOrderThickening

variable {X X' Y Y' S S' : Scheme.{u}}
variable {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
variable [thickeningX : IsThickening iX] [thickeningY : IsThickening iY]
variable [finiteOrderS : IsFiniteOrderThickening iS] [flatX' : Flat pX']
variable (sq : CommSq f iX iY f')
variable (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
variable (pullbackX : IsPullback pX iX iS pX') (pullbackY : IsPullback pY iY iS pY')

include thickeningX thickeningY finiteOrderS flatX'
include sq triangle triangle' pullbackX pullbackY

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is flat if and only if the ambient morphism is flat. -/
theorem flat_iff : Flat f ↔ Flat f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is an isomorphism if and only if the ambient morphism is an isomorphism. -/
theorem isIso_iff : IsIso f ↔ IsIso f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is an open immersion if and only if the ambient morphism is an open immersion. -/
theorem isOpenImmersion_iff : IsOpenImmersion f ↔ IsOpenImmersion f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is quasi-compact if and only if the ambient morphism is quasi-compact. -/
theorem quasiCompact_iff : QuasiCompact f ↔ QuasiCompact f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is universally closed if and only if the ambient morphism is universally closed. -/
theorem universallyClosed_iff : UniversallyClosed f ↔ UniversallyClosed f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is separated if and only if the ambient morphism is separated. -/
theorem isSeparated_iff : IsSeparated f ↔ IsSeparated f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is quasi-separated if and only if the ambient morphism is quasi-separated. -/
theorem quasiSeparated_iff : QuasiSeparated f ↔ QuasiSeparated f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is a monomorphism if and only if the ambient morphism is a monomorphism. -/
theorem mono_iff : Mono f ↔ Mono f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is surjective if and only if the ambient morphism is surjective. -/
theorem surjective_iff : Surjective f ↔ Surjective f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is universally injective if and only if the ambient morphism is universally injective. -/
theorem universallyInjective_iff : UniversallyInjective f ↔ UniversallyInjective f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is affine if and only if the ambient morphism is affine. -/
theorem isAffineHom_iff : IsAffineHom f ↔ IsAffineHom f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is locally of finite type if and only if the ambient morphism is locally of finite type. -/
theorem locallyOfFiniteType_iff : LocallyOfFiniteType f ↔ LocallyOfFiniteType f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is locally quasi-finite if and only if the ambient morphism is locally quasi-finite. -/
theorem locallyQuasiFinite_iff : LocallyQuasiFinite f ↔ LocallyQuasiFinite f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is locally of finite presentation if and only if the ambient morphism is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_iff :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
has relative dimension `d` if and only if the ambient morphism has relative dimension `d`. -/
theorem relativeDimension_iff (d : ℕ) :
    Scheme.Hom.RelativeDimension f d ↔ Scheme.Hom.RelativeDimension f' d := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is universally open if and only if the ambient morphism is universally open. -/
theorem universallyOpen_iff : UniversallyOpen f ↔ UniversallyOpen f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is syntomic if and only if the ambient morphism is syntomic. -/
theorem syntomic_iff : Syntomic f ↔ Syntomic f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is smooth if and only if the ambient morphism is smooth. -/
theorem smooth_iff : Smooth f ↔ Smooth f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is unramified if and only if the ambient morphism is unramified. -/
theorem unramified_iff : Unramified f ↔ Unramified f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is étale if and only if the ambient morphism is étale. -/
theorem etale_iff : Etale f ↔ Etale f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is proper if and only if the ambient morphism is proper. -/
theorem isProper_iff : IsProper f ↔ IsProper f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is integral if and only if the ambient morphism is integral. -/
theorem isIntegralHom_iff : IsIntegralHom f ↔ IsIntegralHom f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is finite if and only if the ambient morphism is finite. -/
theorem isFinite_iff : IsFinite f ↔ IsFinite f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is finite locally free if and only if the ambient morphism is finite locally free. -/
theorem isFiniteLocallyFree_iff : IsFiniteLocallyFree f ↔ IsFiniteLocallyFree f' := sorry

/-- In a cartesian diagram over a finite-order thickening of the base, the closed-fiber morphism
is finite locally free of rank `d` if and only if the ambient morphism is finite locally free of
rank `d`. -/
theorem isFiniteLocallyFreeOfRank_iff (d : ℕ) :
    IsFiniteLocallyFreeOfRank f d ↔ IsFiniteLocallyFreeOfRank f' d := sorry

end AlgebraicGeometry.IsFiniteOrderThickening
