module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.FiniteOrderDeformation
import StacksCheckRecall

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
variable (d : ℕ)

/- Lemma 37.10.3 (1): flatness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.flat_iff sq triangle triangle' pullbackX pullbackY :
    Flat f ↔ Flat f')

/- Lemma 37.10.3 (2): being an isomorphism is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isIso_iff sq triangle triangle' pullbackX pullbackY :
    IsIso f ↔ IsIso f')

/- Lemma 37.10.3 (3): being an open immersion is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isOpenImmersion_iff
    sq triangle triangle' pullbackX pullbackY : IsOpenImmersion f ↔ IsOpenImmersion f')

/- Lemma 37.10.3 (4): quasi-compactness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.quasiCompact_iff
    sq triangle triangle' pullbackX pullbackY : QuasiCompact f ↔ QuasiCompact f')

/- Lemma 37.10.3 (5): universal closedness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.universallyClosed_iff
    sq triangle triangle' pullbackX pullbackY : UniversallyClosed f ↔ UniversallyClosed f')

/- Lemma 37.10.3 (6): separatedness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isSeparated_iff
    sq triangle triangle' pullbackX pullbackY : IsSeparated f ↔ IsSeparated f')

/- Lemma 37.10.3 (7): quasi-separatedness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.quasiSeparated_iff
    sq triangle triangle' pullbackX pullbackY : QuasiSeparated f ↔ QuasiSeparated f')

/- Lemma 37.10.3 (8): being a monomorphism is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.mono_iff sq triangle triangle' pullbackX pullbackY :
    Mono f ↔ Mono f')

/- Lemma 37.10.3 (9): surjectivity is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.surjective_iff
    sq triangle triangle' pullbackX pullbackY : Surjective f ↔ Surjective f')

/- Lemma 37.10.3 (10): universal injectivity is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.universallyInjective_iff
    sq triangle triangle' pullbackX pullbackY :
    UniversallyInjective f ↔ UniversallyInjective f')

/- Lemma 37.10.3 (11): affineness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isAffineHom_iff
    sq triangle triangle' pullbackX pullbackY : IsAffineHom f ↔ IsAffineHom f')

/- Lemma 37.10.3 (12): local finite type is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.locallyOfFiniteType_iff
    sq triangle triangle' pullbackX pullbackY : LocallyOfFiniteType f ↔ LocallyOfFiniteType f')

/- Lemma 37.10.3 (13): local quasi-finiteness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.locallyQuasiFinite_iff
    sq triangle triangle' pullbackX pullbackY : LocallyQuasiFinite f ↔ LocallyQuasiFinite f')

/- Lemma 37.10.3 (14): local finite presentation is invariant in this deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.locallyOfFinitePresentation_iff
    sq triangle triangle' pullbackX pullbackY :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation f')

/- Lemma 37.10.3 (15): relative dimension is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.relativeDimension_iff
    sq triangle triangle' pullbackX pullbackY d :
    Scheme.Hom.RelativeDimension f d ↔ Scheme.Hom.RelativeDimension f' d)

/- Lemma 37.10.3 (16): universal openness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.universallyOpen_iff
    sq triangle triangle' pullbackX pullbackY : UniversallyOpen f ↔ UniversallyOpen f')

/- Lemma 37.10.3 (17): syntomicity is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.syntomic_iff
    sq triangle triangle' pullbackX pullbackY : Syntomic f ↔ Syntomic f')

/- Lemma 37.10.3 (18): smoothness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.smooth_iff sq triangle triangle' pullbackX pullbackY :
    Smooth f ↔ Smooth f')

/- Lemma 37.10.3 (19): unramifiedness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.unramified_iff
    sq triangle triangle' pullbackX pullbackY : Unramified f ↔ Unramified f')

/- Lemma 37.10.3 (20): étaleness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.etale_iff sq triangle triangle' pullbackX pullbackY :
    Etale f ↔ Etale f')

/- Lemma 37.10.3 (21): properness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isProper_iff
    sq triangle triangle' pullbackX pullbackY : IsProper f ↔ IsProper f')

/- Lemma 37.10.3 (22): integrality is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isIntegralHom_iff
    sq triangle triangle' pullbackX pullbackY : IsIntegralHom f ↔ IsIntegralHom f')

/- Lemma 37.10.3 (23): finiteness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isFinite_iff sq triangle triangle' pullbackX pullbackY :
    IsFinite f ↔ IsFinite f')

/- Lemma 37.10.3 (24): finite local freeness is invariant in this finite-order deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isFiniteLocallyFree_iff
    sq triangle triangle' pullbackX pullbackY :
    IsFiniteLocallyFree f ↔ IsFiniteLocallyFree f')

/- Lemma 37.10.3 (25): finite local freeness of rank `d` is invariant in this deformation. -/
@[stacks 06AG] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isFiniteLocallyFreeOfRank_iff
    sq triangle triangle' pullbackX pullbackY d :
    IsFiniteLocallyFreeOfRank f d ↔ IsFiniteLocallyFreeOfRank f' d)

end AlgebraicGeometry.IsFiniteOrderThickening
