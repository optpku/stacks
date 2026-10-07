module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_34_2_Equivalence
public import stacks_project.Chap85.Lemma_85_34_2_Pullback
public import stacks_project.Chap85.Lemma_85_34_2_QCoh

/-!
# Lemma 85.34.2

Let `S` be a scheme, `X` an algebraic space over `S`, and `U` a simplicial
algebraic space over `S`, with augmentation `a : U ⟶ X`. If `a` is an fppf
hypercovering of `X`, then `a^* : QCoh(𝒪_X) ⥤ QCoh(𝒪_U)` is an equivalence,
fully faithful, with quasi-inverse `a_*`. Here `a` is the Section 85.32
spaces-étale augmentation of ringed topoi.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Lemma 85.34.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `U`
be a simplicial algebraic space over `S`. Let `a : U ⟶ X` be an augmentation. If `a`
is an fppf hypercovering of `X`, then `a^* : QCoh(𝒪_X) ⥤ QCoh(𝒪_U)` is an equivalence
fully faithful with quasi-inverse given by `a_*`. Here `a : Sh(U_étale) ⟶ Sh(X_étale)`
is the Section 85.32 spaces-étale augmentation `spacesEtaleAugmentationRinged`, and
`QCoh(𝒪_X)` (resp. `QCoh(𝒪_U)`) is the category of quasi-coherent modules on
`spacesRingedSite X` (resp. `etaleTotalRingedSite U`). -/
@[stacks 0DHD]
def qcohEquivalence (ha : IsFppfHypercovering a) :
    (spacesQuasiCoherentModuleProperty X).FullSubcategory ≌ QCoh U :=
  qcohDescent a ha

/-- The forward functor of `qcohEquivalence` is `a^*` restricted to quasi-coherent
modules. -/
theorem qcohEquivalence_functor (ha : IsFppfHypercovering a) :
    (qcohEquivalence a ha).functor = QCoh.pullback a :=
  sorry

/-- The inverse functor of `qcohEquivalence` is `a_*` on quasi-coherent modules. -/
theorem qcohEquivalence_inverse (ha : IsFppfHypercovering a) :
    (qcohEquivalence a ha).inverse = QCoh.pushforward a ha :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
