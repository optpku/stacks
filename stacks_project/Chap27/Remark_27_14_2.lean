/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import stacks_project.Chap27.Remark_27_9_2
public import stacks_project.Chap27.Lemma_27_14_1
public import stacks_project.Chap27.Remark_27_14_2_InvertibleLocus

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Scheme.Modules.Invertible
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.TensorCounterexample

variable (k : Type u) [Field k]

/-- The weighted substitution preserves degree when the source variables have weights
`1`, `2`, and `3` and the target variables all have degree `1`. -/
theorem powerMap_mem (d : ℕ) (f : PolynomialRing k) (hf : f ∈ grading k d) :
    MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i : Fin 3 ↦ MvPolynomial.X i ^ (i.val + 1)) f ∈
      ProjectiveSpace.grading k 2 d := sorry

/-- The graded substitution from the weighted polynomial ring to the standard homogeneous
coordinate ring of `ℙ²_k`. -/
def powerMap : grading k →+*ᵍ ProjectiveSpace.grading k 2 where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin 3 ↦ MvPolynomial.X i ^ (i.val + 1))
  map_mem := powerMap_mem k _ _

/-- The graded substitution sends its `i`-th variable to the `(i.val + 1)`-st power of the
corresponding standard coordinate. -/
theorem powerMap_X (i : Fin 3) :
    powerMap k (MvPolynomial.X i) = MvPolynomial.X i ^ (i.val + 1) := sorry

/-- The degree-one twist in a chosen presentation of `ℙ²_k` is invertible. -/
instance instInvertibleProjectivePlaneTwistOne
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    Scheme.Modules.Invertible (P.actualTwist 1) := sorry

/-- The tensor powers of the projective-plane degree-one twist carry their canonical graded
commutative-ring structure. -/
noncomputable instance instGCommRingProjectivePlaneTwistOne
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    DirectSum.GCommRing (RingedSpace.GradedSections.degree (P.actualTwist 1)) :=
  @RingedSpace.GradedSections.instGCommRing
    (ProjectiveSpace.scheme k 2).toRingedSpace (P.actualTwist 1)
    instRingedSpaceIsInvertible

/-- The tensor-power sections of the projective-plane degree-one twist form a commutative ring. -/
noncomputable instance instCommRingProjectivePlaneTwistOne
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    CommRing (RingedSpace.GradedSections.ring (P.actualTwist 1)) :=
  DirectSum.commRing (RingedSpace.GradedSections.degree (P.actualTwist 1))

/-- A scalar in `k`, viewed as a degree-zero element of the tensor-power section ring on
`ℙ²_k`. -/
noncomputable def baseSection
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) (r : k) :
    RingedSpace.GradedSections.ring (P.actualTwist 1) :=
  DirectSum.of (RingedSpace.GradedSections.degree (P.actualTwist 1)) 0
    (RingedSpace.GradedSections.scalar (P.actualTwist 1)
      ((ProjectiveSpace.globalSectionsComparison k 2).hom r))

/-- The degree-zero scalar construction preserves zero. -/
theorem baseSection_zero
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    baseSection k P 0 = 0 := sorry

/-- The degree-zero scalar construction preserves one. -/
theorem baseSection_one
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    baseSection k P 1 = 1 := sorry

/-- The degree-zero scalar construction preserves addition. -/
theorem baseSection_add
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) (r s : k) :
    baseSection k P (r + s) = baseSection k P r + baseSection k P s := sorry

/-- The degree-zero scalar construction preserves multiplication. -/
theorem baseSection_mul
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) (r s : k) :
    baseSection k P (r * s) = baseSection k P r * baseSection k P s := sorry

/-- The canonical coefficient homomorphism from `k` to the tensor-power section ring on
`ℙ²_k`. -/
noncomputable def baseSectionHom
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    k →+* RingedSpace.GradedSections.ring (P.actualTwist 1) where
  toFun := baseSection k P
  map_zero' := baseSection_zero k P
  map_one' := baseSection_one k P
  map_add' := baseSection_add k P
  map_mul' := baseSection_mul k P

/-- The standard coordinate `X_i`, regarded as a degree-one section of the tensor-power
section ring of `P.actualTwist 1` on `ℙ²_k`. -/
noncomputable def coordinateSection
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) (i : Fin 3) :
    RingedSpace.GradedSections.ring (P.actualTwist 1) :=
  DirectSum.of (RingedSpace.GradedSections.degree (P.actualTwist 1)) 1
    ((Scheme.Modules.globalSectionsMap
        (RingedSpace.TensorPower.oneIso (P.actualTwist 1)).inv).hom
      ((P.actualSectionMap 1).hom
        ⟨MvPolynomial.X i, ProjectiveSpace.coordinate_mem_grading_one 2 i⟩))

/-- The source map `ψ` is the concrete substitution `A ↦ X₀`, `B ↦ X₁²`, `C ↦ X₂³`,
followed by the canonical map to the tensor-power section ring of `P.actualTwist 1` on `ℙ²_k`. -/
noncomputable def psi
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    PolynomialRing k →+* RingedSpace.GradedSections.ring (P.actualTwist 1) :=
  (MvPolynomial.eval₂Hom (baseSectionHom k P) (coordinateSection k P)).comp
    (powerMap k).toRingHom

/-- The concrete map `ψ` sends its `i`-th weighted variable to the `(i.val + 1)`-st power of
the corresponding degree-one section. -/
theorem psi_X
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) (i : Fin 3) :
    psi k P (MvPolynomial.X i) = coordinateSection k P i ^ (i.val + 1) := sorry

/-- The concrete map `psi k P` preserves the weighted grading. -/
theorem psiPreservesDegree
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    projSectionRingMapPreservesDegree (grading k) (P.actualTwist 1) (psi k P) := sorry

/-- The natural domain of `psi k P` agrees with the natural domain of the direct graded
projective-spectrum map induced by `powerMap k`. -/
theorem sectionRingDomain_eq_projMapDomain
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2)) :
    projSectionRingDomain (grading k) (P.actualTwist 1) (psi k P)
      (psiPreservesDegree k P) = projMapDomain (powerMap k) := sorry

/-- The canonical morphism from projective `2`-space to the weighted projective spectrum
induced by the coordinate-power substitution. -/
noncomputable abbrev map :
    (projMapDomain (powerMap k)).toScheme ⟶ Proj (grading k) :=
  projMapMap (powerMap k)

/-- The canonical projective-spectrum map induced by the weighted substitution is defined on all
of projective `2`-space. -/
theorem powerMapDomain_eq_top :
    projMapDomain (powerMap k) = ⊤ := sorry

/-- The canonical map `map k` is the morphism `r_{P.actualTwist 1, psi k P}` characterized by
Lemma 27.14.1: the inverse image of every positive-degree basic open `D₊(f)` is the locus where
the germ of the corresponding section `psi k P f` does not vanish. The equality
`sectionRingDomain_eq_projMapDomain` identifies its source with `U(psi k P)`. -/
theorem mapSectionRingCompatibility
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2))
    (f : PositiveHomogeneous (grading k))
    (x : (projMapDomain (powerMap k)).toScheme) :
    (map k).base x ∈ Proj.basicOpen (grading k) f.1 ↔
      (projMapDomain (powerMap k)).ι.base x ∈
        sectionNonvanishingSet (RingedSpace.TensorPower.sheaf (P.actualTwist 1) f.degree)
          (projSectionRingDegreeSection (grading k) (P.actualTwist 1) (psi k P) f.degree
            ⟨f.1, PositiveHomogeneous.mem_degree f⟩) := sorry

/-- Remark 27.14.2 (1): the canonical morphism induced by the substitution
`A ↦ X₀`, `B ↦ X₁²`, `C ↦ X₂³` is surjective. -/
@[stacks 01NL]
instance instSurjectiveMap : Surjective (map k) := sorry

/-- The invertibility locus of the degree-one twist on the weighted projective spectrum is
not all of that spectrum. -/
theorem twistOne_invertibleLocus_ne_top
    (Q : ProjTwistPresentation (grading k)) :
    Scheme.Modules.invertibleLocus (Q.actualTwist 1) ≠ ⊤ := sorry

/-- Remark 27.14.2 (2): the image of the canonical morphism induced by the substitution
`A ↦ X₀`, `B ↦ X₁²`, `C ↦ X₂³` is not contained in the locus where the weighted
projective twist `𝒪(1)` is invertible. -/
@[stacks 01NL]
theorem range_not_subset_invertibleLocus
    (Q : ProjTwistPresentation (grading k)) :
    ¬ Set.range (map k).base ⊆
      (Scheme.Modules.invertibleLocus (Q.actualTwist 1) : Set (Proj (grading k))) := sorry

end AlgebraicGeometry.Proj.TensorCounterexample
