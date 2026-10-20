module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor

/-!
# Dual numbers in under-categories

Residue maps, dual-number restrictions, and the dual-number pullback with its
sum and scaling morphisms over an arbitrary Artinian local algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The object `A → k` of `Under A`, i.e. the canonical `C_A`-object given by `toResidue`. -/
def residueUnder (A : ArtinianLocalAlgCat Λ k) : Under A :=
  Under.mk (toResidue A)

/-- The structure map of `residueUnder A` is `toResidue A`. -/
theorem residueUnder_hom (A : ArtinianLocalAlgCat Λ k) :
    (residueUnder A).hom = toResidue A := rfl

/-- The object `A → k[ε]` of `Under A`, obtained by composing `toResidue` with
`residueToDualNumber`. -/
def dualNumberUnder (A : ArtinianLocalAlgCat Λ k) : Under A :=
  Under.mk (toResidue A ≫ residueToDualNumber Λ k)

/-- The structure map of `dualNumberUnder A` is `toResidue A ≫ residueToDualNumber`. -/
theorem dualNumberUnder_hom (A : ArtinianLocalAlgCat Λ k) :
    (dualNumberUnder A).hom = toResidue A ≫ residueToDualNumber Λ k := rfl

/-- Triangle identity for the dual-number restriction of an `Under A`-object. -/
theorem dualNumberToResidueUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ residueToDualNumber Λ k) ≫ dualNumberToResidue Λ k = toResidue A := sorry

/-- The restriction morphism `(A → k[ε]) ⟶ (A → k)` in `Under A`. -/
def dualNumberToResidueUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberUnder A ⟶ residueUnder A :=
  Under.homMk (dualNumberToResidue Λ k) (dualNumberToResidueUnder_w A)

/-- The underlying algebra map of `dualNumberToResidueUnder` is `dualNumberToResidue`. -/
theorem dualNumberToResidueUnder_right (A : ArtinianLocalAlgCat Λ k) :
    (dualNumberToResidueUnder A).right = dualNumberToResidue Λ k := rfl

/-- The dual-number restriction in `Under A` is surjective on underlying algebra maps. -/
theorem dualNumberToResidueUnder_surjective (A : ArtinianLocalAlgCat Λ k) :
    Function.Surjective (dualNumberToResidueUnder A).right.hom := sorry

/-- The unique structure map `k → k[ε] ×_k k[ε]`, as the composite of `residueToDualNumber`
with the canonical section of the first projection. -/
def dualNumberPullbackFromResidue :
    residue Λ k ⟶ dualNumberPullback (dualNumber Λ k) :=
  residueToDualNumber Λ k ≫ dualNumberPullbackSection (dualNumber Λ k)

/-- `dualNumberPullbackFromResidue` is the section of `dualNumberPullbackFst` after
`residueToDualNumber`. -/
theorem dualNumberPullbackFromResidue_comp_fst :
    dualNumberPullbackFromResidue ≫ dualNumberPullbackFst (dualNumber Λ k) =
      residueToDualNumber Λ k := sorry

/-- The object `A → k[ε] ×_k k[ε]` of `Under A`. -/
def dualNumberPullbackUnder (A : ArtinianLocalAlgCat Λ k) : Under A :=
  Under.mk (toResidue A ≫ dualNumberPullbackFromResidue)

/-- The structure map of `dualNumberPullbackUnder A` factors through
`dualNumberPullbackFromResidue`. -/
theorem dualNumberPullbackUnder_hom (A : ArtinianLocalAlgCat Λ k) :
    (dualNumberPullbackUnder A).hom = toResidue A ≫ dualNumberPullbackFromResidue := rfl

/-- Triangle identity for the first projection of `k[ε] ×_k k[ε]` in `Under A`. -/
theorem dualNumberPullbackFstUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ dualNumberPullbackFromResidue) ≫
        dualNumberPullbackFst (dualNumber Λ k) =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- The first projection `(A → k[ε] ×_k k[ε]) ⟶ (A → k[ε])` in `Under A`. -/
def dualNumberPullbackFstUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberPullbackUnder A ⟶ dualNumberUnder A :=
  Under.homMk (dualNumberPullbackFst (dualNumber Λ k)) (dualNumberPullbackFstUnder_w A)

/-- Triangle identity for the second projection of `k[ε] ×_k k[ε]` in `Under A`. -/
theorem dualNumberPullbackSndUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ dualNumberPullbackFromResidue) ≫
        dualNumberPullbackSnd (dualNumber Λ k) =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- The second projection `(A → k[ε] ×_k k[ε]) ⟶ (A → k[ε])` in `Under A`. -/
def dualNumberPullbackSndUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberPullbackUnder A ⟶ dualNumberUnder A :=
  Under.homMk (dualNumberPullbackSnd (dualNumber Λ k)) (dualNumberPullbackSndUnder_w A)

/-- Triangle identity for the sum map of `k[ε] ×_k k[ε]` in `Under A`. -/
theorem dualNumberSumUnder_w (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A ≫ dualNumberPullbackFromResidue) ≫ dualNumberSum =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- The sum morphism `(A → k[ε] ×_k k[ε]) ⟶ (A → k[ε])` in `Under A`. -/
def dualNumberSumUnder (A : ArtinianLocalAlgCat Λ k) :
    dualNumberPullbackUnder A ⟶ dualNumberUnder A :=
  Under.homMk dualNumberSum (dualNumberSumUnder_w A)

/-- Triangle identity for dual-number scaling in `Under A`. -/
theorem dualNumberSMulUnder_w (A : ArtinianLocalAlgCat Λ k) (r : k) :
    (toResidue A ≫ residueToDualNumber Λ k) ≫ dualNumberScaleHom Λ r =
      toResidue A ≫ residueToDualNumber Λ k := sorry

/-- Scaling by `r : k` as an endomorphism of `A → k[ε]` in `Under A`. -/
def dualNumberSMulUnder (A : ArtinianLocalAlgCat Λ k) (r : k) :
    dualNumberUnder A ⟶ dualNumberUnder A :=
  Under.homMk (dualNumberScaleHom Λ r) (dualNumberSMulUnder_w A r)

/-- The dual-number fibre-product square, lifted to `Under A`. -/
theorem isPullback_dualNumberUnder (A : ArtinianLocalAlgCat Λ k) :
    IsPullback (dualNumberPullbackFstUnder A) (dualNumberPullbackSndUnder A)
      (dualNumberToResidueUnder A) (dualNumberToResidueUnder A) := sorry

end ArtinianLocalAlgCat

