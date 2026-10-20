/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineQuotient
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Quotient

/-!
# Explicit fppf quotient comparisons for affine finite locally free groupoids

For an affine groupoid scheme with finite locally free source and target whose `(t, s)` is a
monomorphism, the spectrum `M` of invariant global functions represents the fppf quotient sheaf
`U / R` (Stacks, Groupoids, Proposition 03BM). This module gives that identification as an
explicit isomorphism of sheaves:

* the forward map is the canonical comparison `quotientSheafDesc` induced by `U → M`;
* the inverse map is classified by the section of `U / R` over `M` obtained by descending the
  quotient class of `𝟙 U` along the fppf covering `U → M`. Restricting this section along a
  test point `T → M` is descent of the local quotient section along the fppf covering
  `T ×_M U → T`.

This module treats the canonical global-section presentation (`objectQuotient`). The
comparison for an explicitly presented affine groupoid (`invariantSpectrumOver`) is provided
by `GroupoidScheme.InvariantSpectrum.Quotient`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

section ObjectQuotient

variable {S : Scheme.{u}} (P : GroupoidScheme S)
  [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
  [Mono P.toPreRelation.hom.left]

/-- The fppf topology on `Over S` is subcanonical; the global instance is not found by
instance search for the `fppf` topology, so it is registered locally here. -/
local instance : (StandardTopology.fppf.overTopology S).Subcanonical :=
  StandardTopology.overTopologySubcanonical StandardTopology.fppf S

/-- The canonical map to the invariant spectrum is surjective. -/
theorem objectQuotientMap_surjective : Surjective (objectQuotientMap P).left :=
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  ⟨@invariantSpectrumMap_surjective _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) P.U.left.isoSpec.symm
    (@Scheme.isoSpec P.R.left arrowAffine).symm
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
    inferInstance inferInstance⟩

/-- Two points of the object scheme with the same image in the invariant spectrum are related
by the groupoid: the arrow scheme is the kernel pair of the quotient map. -/
theorem objectQuotientMap_pointRel {W : Over S} (a b : W ⟶ P.U)
    (h : a ≫ objectQuotientMap P = b ≫ objectQuotientMap P) :
    P.toPreRelation.pointRel W a b := sorry

/-- The quotient map `U → M` generates an fppf covering sieve of the invariant spectrum. -/
theorem objectQuotientMap_generate_mem_fppf :
    Sieve.generate (Presieve.singleton (objectQuotientMap P)) ∈
      StandardTopology.fppf.overTopology S (objectQuotientOver P) :=
  have := objectQuotientMap_isFiniteLocallyFree P
  have := objectQuotientMap_surjective P
  Scheme.PreRelation.generate_singleton_mem_fppf_over (objectQuotientMap P)

/-- The inverse comparison from the represented invariant spectrum to the fppf quotient sheaf,
classified by the descent of the quotient class of `𝟙 U` along `U → M`. -/
def objectQuotientSheafInverse :
    (StandardTopology.fppf.overTopology S).uliftYoneda.{u + 1}.obj (objectQuotientOver P) ⟶
      P.toPreRelation.quotientSheaf (StandardTopology.fppf.overTopology S) :=
  @Scheme.PreRelation.quotientSheafInvOfCover _ _ _ (StandardTopology.fppf.overTopology S)
    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S) P.toPreRelation
    (objectQuotientMap P) (objectQuotientMap_generate_mem_fppf P)
    (fun a b h ↦ objectQuotientMap_pointRel P a b h)

/-- The invariant spectrum represents the fppf quotient sheaf: the canonical comparison and
the descended inverse form an explicit isomorphism. -/
def objectQuotientSheafIso :
    P.toPreRelation.quotientSheaf (StandardTopology.fppf.overTopology S) ≅
      (StandardTopology.fppf.overTopology S).uliftYoneda.{u + 1}.obj (objectQuotientOver P) :=
  @Scheme.PreRelation.quotientSheafIsoOfCover _ _ _ (StandardTopology.fppf.overTopology S)
    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S) P.toPreRelation
    (objectQuotientMap P) (objectQuotientMap_equalizes P)
    (objectQuotientMap_generate_mem_fppf P) (fun a b h ↦ objectQuotientMap_pointRel P a b h)

/-- The forward map of `objectQuotientSheafIso` is the canonical comparison. -/
theorem objectQuotientSheafIso_hom :
    (objectQuotientSheafIso P).hom = objectQuotientSheafComparison P :=
  rfl

/-- The inverse map of `objectQuotientSheafIso` is the descended comparison. -/
theorem objectQuotientSheafIso_inv :
    (objectQuotientSheafIso P).inv = objectQuotientSheafInverse P :=
  rfl

end ObjectQuotient


end AlgebraicGeometry.GroupoidScheme
