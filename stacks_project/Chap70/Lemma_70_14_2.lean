module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap70.Lemma_70_14_2_Stalk
public import stacks_project.Chap70.Lemma_70_14_2_Torsion

/-!
# Quasi-coherence of the subsheaf of sections annihilated by a finite type ideal

On an algebraic space, the étale subsheaf of sections annihilated by a quasi-coherent finite
type ideal sheaf is quasi-coherent, and agrees with the naive annihilator on affine étale
objects and on geometric-point stalks.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 70.14.2 (1): if `I ⊂ 𝒪_X` is a quasi-coherent finite type ideal sheaf on an algebraic
space `X` over a scheme `S` and `ℱ` is a quasi-coherent `𝒪_X`-module, then the subsheaf of
sections annihilated by `I` is quasi-coherent. -/
@[stacks 0856, instance]
instance idealTorsionSubsheaf_isQuasicoherent (I : IdealSubobject X) (ℱ : X.Modules)
    [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType] [ℱ.IsQuasicoherent] :
    (idealTorsionSubsheaf I ℱ).IsQuasicoherent :=
  sorry

/-- Lemma 70.14.2 (2): on an affine object of `X_étale`, the image of the torsion inclusion
consists exactly of the sections annihilated by every section of `I` over that object. -/
@[stacks 0856]
theorem range_idealTorsionSubsheafι_app_eq_affine_annihilatedSections
    (I : IdealSubobject X) (ℱ : X.Modules)
    [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType] [ℱ.IsQuasicoherent]
    (U : affineEtaleSite X) :
    Set.range ((idealTorsionSubsheafι I ℱ).val.app (op U.obj)) =
      setOf (fun s ↦ ∀ a, a ∈ SheafOfModules.Subobject.sections I (op U.obj) → a • s = 0) :=
  sorry

/-- A stalk section is annihilated by `I` when every representative over an étale neighborhood
is killed, as a germ, by every section of `I` over that neighborhood. -/
def isAnnihilatedByIdealStalk (I : IdealSubobject X) (ℱ : X.Modules)
    (xbar : GeometricPoint X) (s : stalk xbar ℱ) : Prop :=
  ∀ (N : GeometricPoint.SmallEtaleNeighborhood xbar)
    (a : (I : X.Modules).val.obj (op N.toSite)) (σ : ℱ.val.obj (op N.toSite)),
    toStalk xbar N σ = s →
      stalkSMul xbar N (SheafOfModules.Subobject.inclusionApp I (op N.toSite) a) σ =
        toStalk xbar N 0

/-- Lemma 70.14.2 (3): at a geometric point, the image of the stalk inclusion is the set of
stalk sections annihilated by every germ of `I`. -/
@[stacks 0856]
theorem range_idealTorsionSubsheafι_stalk_eq_annihilatedStalkSections
    (I : IdealSubobject X) (ℱ : X.Modules)
    [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType] [ℱ.IsQuasicoherent]
    (xbar : GeometricPoint X) :
    Set.range (stalkMap xbar (idealTorsionSubsheafι I ℱ)) =
      setOf (isAnnihilatedByIdealStalk I ℱ xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
