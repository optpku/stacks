/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import stacks_project.Chap90.Definition_90_7_3_FormalObject
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject
public import stacks_project.Chap98.«98_3_0_2»

/-!
# Scheme-level formal objects as formal objects of `ℱ_{X, k, x₀}`

A formal object `ξ` of a category fibred in groupoids `X` over `(Sch/S)_fppf`
packages the same data as a Chap90 formal object of the predeformation functor
`ℱ_{X, R/m, ξ₁}` from Section 98.3, after the standing affine-open factorization
of the structure morphism `Spec(R) ⟶ S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S}

/-- Structure morphism `Spec(κ(R)) ⟶ S` of the residue field of a formal object. -/
def residueToS (ξ : FormalObject X) :
    Spec (CommRingCat.of (ResidueField ξ.base.carrier)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (residue ξ.base.carrier)) ≫ ξ.base.toS

/-- `residueToS ξ` is the residue-field spectrum of the complete local base of `ξ`. -/
theorem residueToS_eq (ξ : FormalObject X) :
    residueToS ξ =
      Spec.map (CommRingCat.ofHom (residue ξ.base.carrier)) ≫ ξ.base.toS :=
  sorry

/-- The residue-field point of a formal object is locally of finite type over `S`. -/
instance locallyOfFiniteType_residueToS (ξ : FormalObject X) :
    LocallyOfFiniteType (residueToS ξ) :=
  ξ.base.residue_locallyOfFiniteType

/-- The first stage `ξ₁` lies over `Spec(κ(R)) ⟶ S`. -/
theorem residueFiber_over (ξ : FormalObject X) :
    X.p.obj ξ.stageOne = Over.mk (residueToS ξ) :=
  sorry

/-- The residue fibre object `x₀ = ξ₁` of a formal object. -/
def residueFiber (ξ : FormalObject X) :
    X.p.Fiber (Over.mk (residueToS ξ)) :=
  Fiber.mk (residueFiber_over ξ)

/-- `residueFiber ξ` is the first stage `ξ.stageOne` in the residue fibre. -/
theorem residueFiber_obj (ξ : FormalObject X) :
    Fiber.fiberInclusion.obj (residueFiber ξ) = ξ.stageOne :=
  sorry

/-- The composite `ξ₁ ⟶ ξ_{n+1}` obtained from the forward system of `ξ`. -/
def fromResidue (ξ : FormalObject X) (n : ℕ) :
    ξ.stageOne ⟶ ξ.objects n :=
  (Functor.ofSequence ξ.step).map (homOfLE (Nat.zero_le n))

/-- The stage-zero composite `fromResidue ξ 0` is the identity on `ξ₁`. -/
theorem fromResidue_zero (ξ : FormalObject X) :
    fromResidue ξ 0 = 𝟙 ξ.stageOne :=
  sorry

/-- Successor composites of `fromResidue` are postcomposition with `ξ.step`. -/
theorem fromResidue_succ (ξ : FormalObject X) (n : ℕ) :
    fromResidue ξ (n + 1) = fromResidue ξ n ≫ ξ.step n :=
  sorry

section Predeformation

variable (ξ : FormalObject X)
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [Algebra Λ ξ.base.carrier]
variable [Module.Finite Λ (ResidueField ξ.base.carrier)]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable
  (h_toS :
    Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫ openImmersion =
      ξ.base.toS)

include h_toS

/-- Factorization of the residue-field point `Spec(κ(R)) ⟶ S` through the chosen
affine open, induced by the structure-morphism factorization `h_toS`. -/
theorem residue_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.carrier))) ≫
        openImmersion =
      residueToS ξ :=
  sorry

/-- The `Λ`-algebra structure morphism of the `n`th truncation, composed with the
chosen affine open, recovers `ξ.base.stageOver n` via the quotient of
`algebraMap Λ R` and `h_toS`. -/
theorem predeformationObj_over (n : ℕ) :
    Predeformation.specOver openImmersion
        ((CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl).truncation n) =
      ξ.base.stageOver n :=
  sorry

/-- The category `ℱ_{X, κ(R), ξ₁}` of morphisms `ξ₁ ⟶ x` over Artinian local
`Λ`-algebras. -/
abbrev predeformationCategory :=
  Predeformation.Obj openImmersion (residueToS ξ) (residue_factor ξ openImmersion h_toS)
    X (residueFiber ξ)

/-- `predeformationCategory` is the Section 98.3 object category of `ℱ_{X, κ(R), ξ₁}`. -/
theorem predeformationCategory_eq :
    predeformationCategory ξ openImmersion h_toS =
      Predeformation.Obj openImmersion (residueToS ξ)
        (residue_factor ξ openImmersion h_toS) X (residueFiber ξ) :=
  sorry

/-- Stage `n` of `ξ` as an object `x₀ ⟶ ξ_{n+1}` of `ℱ_{X, κ(R), ξ₁}` over
`Spec(R ⧸ m^{n+1})`. -/
def predeformationObj (n : ℕ) : predeformationCategory ξ openImmersion h_toS where
  base := (CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl).truncation n
  target :=
    Fiber.mk ((ξ.over_obj n).trans (predeformationObj_over ξ openImmersion h_toS n).symm)
  fromResidue := fromResidue ξ n
  over_fromResidue := sorry

/-- Unpacked data of `predeformationObj`: truncation base, fibre object `ξ_{n+1}`,
and the composite from `ξ₁`. -/
theorem predeformationObj_spec (n : ℕ) :
    (predeformationObj ξ openImmersion h_toS n).base =
        (CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl).truncation n ∧
      Fiber.fiberInclusion.obj (predeformationObj ξ openImmersion h_toS n).target =
        ξ.objects n ∧
      (predeformationObj ξ openImmersion h_toS n).fromResidue = fromResidue ξ n ∧
      X.p.IsHomLift
        (Predeformation.specOver_toResidue openImmersion (residueToS ξ)
          (residue_factor ξ openImmersion h_toS)
          (predeformationObj ξ openImmersion h_toS n).base)
        (predeformationObj ξ openImmersion h_toS n).fromResidue :=
  sorry

/-- Inverse-system successor `ξ_{n+2} ⟶ ξ_{n+1}` in `ℱ_{X, κ(R), ξ₁}`, reversing
the original forward step of `ξ`. -/
def predeformationStep (n : ℕ) :
    Predeformation.Hom (predeformationObj ξ openImmersion h_toS (n + 1))
      (predeformationObj ξ openImmersion h_toS n) where
  baseHom := (CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl).truncationMap n
  hom := ξ.step n
  over_hom := sorry
  triangle := sorry

/-- The reversed total-category arrow of `predeformationStep` is the original
forward step of `ξ`. -/
theorem predeformationStep_hom (n : ℕ) :
    (predeformationStep ξ openImmersion h_toS n).hom = ξ.step n :=
  sorry

/-- Stage `n` of `ξ` in the Hom-universe lift of `ℱ_{X, κ(R), ξ₁}`. -/
def predeformationStage (n : ℕ) :
    ULiftHom.{u + 1} (predeformationCategory ξ openImmersion h_toS) :=
  ULiftHom.objUp (predeformationObj ξ openImmersion h_toS n)

/-- `predeformationStage n` is the Hom-universe lift of `predeformationObj n`. -/
theorem predeformationStage_eq (n : ℕ) :
    predeformationStage ξ openImmersion h_toS n =
      ULiftHom.objUp (predeformationObj ξ openImmersion h_toS n) :=
  sorry

/-- Successor transition of Hom-universe lifts of the inverse system of `ξ`. -/
def predeformationStageMap (n : ℕ) :
    predeformationStage ξ openImmersion h_toS (n + 1) ⟶
      predeformationStage ξ openImmersion h_toS n :=
  (ULiftHom.up :
      predeformationCategory ξ openImmersion h_toS ⥤
        ULiftHom.{u + 1} (predeformationCategory ξ openImmersion h_toS)).map
    (predeformationStep ξ openImmersion h_toS n)

/-- Forgetting Hom-universe lift recovers `predeformationStep`. -/
theorem predeformationStageMap_down (n : ℕ) :
    ULiftHom.down.map (predeformationStageMap ξ openImmersion h_toS n) =
      predeformationStep ξ openImmersion h_toS n :=
  sorry

/-- Hom-universe lift of the forgetful functor of `ℱ_{X, κ(R), ξ₁}`, matching the
object/Hom universe of Chap90 `FormalObject`. -/
def predeformationProjection :
    ULiftHom.{u + 1}
        (Predeformation.Obj openImmersion (residueToS ξ)
          (residue_factor ξ openImmersion h_toS) X (residueFiber ξ)) ⥤
      ArtinianLocalAlgCat Λ (ResidueField ξ.base.carrier) :=
  ULiftHom.down ⋙
    Predeformation.predeformationFunctor X openImmersion (residueToS ξ)
      (residue_factor ξ openImmersion h_toS) (residueFiber ξ)

/-- `predeformationProjection` is `ULiftHom.down` followed by the Section 98.3
predeformation functor. -/
theorem predeformationProjection_eq :
    predeformationProjection ξ openImmersion h_toS =
      ULiftHom.down ⋙
        Predeformation.predeformationFunctor X openImmersion (residueToS ξ)
          (residue_factor ξ openImmersion h_toS) (residueFiber ξ) :=
  sorry

/-- The Chap90 formal object of `ℱ_{X, κ(R), ξ₁}` carried by a scheme-level
formal object `ξ`, with `k = ResidueField R` and `x₀ = ξ.stageOne`. -/
def toPredeformation :
    _root_.FormalObject (predeformationProjection ξ openImmersion h_toS) where
  base := CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl
  system := Functor.ofOpSequence (predeformationStageMap ξ openImmersion h_toS)
  over_obj := sorry
  over_step := sorry

/-- The complete local base of `toPredeformation ξ` has the same carrier as `ξ`. -/
theorem toPredeformation_base :
    (toPredeformation ξ openImmersion h_toS).base.carrier = ξ.base.carrier :=
  sorry

/-- Stage `n` of `toPredeformation ξ` lies over the `n`th truncation of `R`, and
the successor lifts the truncation projection. -/
theorem toPredeformation_spec (n : ℕ) :
    (predeformationProjection ξ openImmersion h_toS).obj
          ((toPredeformation ξ openImmersion h_toS).system.family n) =
        (CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl).truncation n ∧
      (predeformationProjection ξ openImmersion h_toS).IsHomLift
        ((CompleteLocalAlgCat.of ξ.base.carrier AlgEquiv.refl).truncationMap n)
        ((toPredeformation ξ openImmersion h_toS).system.stepMap n) :=
  sorry

end Predeformation

end AlgebraicGeometry.GroupoidsOver.FormalObject
