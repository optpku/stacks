/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating
public import ReasLib.AlgebraicTopology.Cech.Conerve.Coprojection
public import ReasLib.RingTheory.Sequence.Koszul.Power
import Mathlib.Tactic.CrossRefAttribute

/-!
# The powered Koszul direct system for the extended Cech complex

This owner records the source-facing sequential system in Lemma 15.29.6.  The stages are
cohomologically reindexed over `ℕ`; in degree `p` the exterior degree is `r - p`, and the
transition is multiplication by the product of the complementary family members.  This is the
direct system used in the Stacks proof, rather than the inverse system on `ℕᵒᵖ` used for a different
localization API.

@stack 0913
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape ModuleCat Set
open scoped KoszulComplex

universe u

namespace LocalizedModule.Away.Cech.Koszul

variable {R : Type u} [CommRing R]
variable {r : ℕ}

/-! ### Stages and their complementary grading -/

/-- Lemma 15.29.6 (Stacks `0913`): the powered Koszul stage in cochain grading. -/
@[stacks 0913 "cohomologically reindexed powered Koszul stage"]
noncomputable abbrev stage (f : Fin r → R) (n : ℕ) :
    CochainComplex (ModuleCat R) ℕ :=
  (((KoszulComplex.powerComplex f n).extend (embeddingUpIntLE (r : ℤ))).restriction
    embeddingUpNat)

/-- Lemma 15.29.6 (Stacks `0913`): the reindexing identifies degree `p` with degree `r - p`. -/
@[stacks 0913 "Koszul stage degree reindexing"]
theorem stageIndex_eq (p : ℕ) (hp : p ≤ r) :
    (embeddingUpIntLE (r : ℤ)).f (r - p) = (p : ℤ) := sorry

/-- The standard exterior basis on the finite coordinate module. -/
@[stacks 0913 "exterior basis for the powered Koszul system"]
noncomputable abbrev exteriorBasis (p : ℕ) :
    Module.Basis (powersetCard (Fin r) p) R (⋀[R]^p (Fin r → R)) :=
  (Pi.basisFun R (Fin r)).exteriorPower p

/-- Lemma 15.29.6 (Stacks `0913`): the complementary-product map in exterior degree `r - p`. -/
@[stacks 0913 "complementary-product exterior transition"]
noncomputable def complementStep (f : Fin r → R) (p : ℕ) :
    ⋀[R]^(r - p) (Fin r → R) →ₗ[R] ⋀[R]^(r - p) (Fin r → R) :=
  Module.Basis.constr (exteriorBasis (r - p)) R
    (fun s ↦ (Finset.prod s.1ᶜ f) • exteriorBasis (r - p) s)

/-- The canonical componentwise identification of a reindexed stage with an exterior power. -/
@[stacks 0913 "Koszul stage component identification"]
noncomputable def stageIso (f : Fin r → R) (n p : ℕ) (hp : p ≤ r) :
    (stage f n).X p ≅ ModuleCat.of R (⋀[R]^(r - p) (Fin r → R)) :=
  (((KoszulComplex.powerComplex f n).extend (embeddingUpIntLE (r : ℤ))).restrictionXIso
      embeddingUpNat rfl) ≪≫
    ((KoszulComplex.powerComplex f n).extendXIso (embeddingUpIntLE (r : ℤ))
      (stageIndex_eq (r := r) p hp))

/-- Lemma 15.29.6 (Stacks `0913`): the degree-`p` component of the direct transition. -/
@[stacks 0913 "powered Koszul direct transition component"]
noncomputable def stepComponent (f : Fin r → R) (n p : ℕ) :
    (stage f n).X p ⟶ (stage f (n + 1)).X p :=
  if hp : p ≤ r then
    (stageIso f n p hp).hom ≫
      ModuleCat.ofHom (complementStep f p) ≫
      (stageIso f (n + 1) p hp).inv
  else
    0

/-- The complementary-product components commute with the reindexed Koszul differentials. -/
@[stacks 0913 "direct transition commutativity"]
theorem stepComponent_comm (f : Fin r → R) (n : ℕ) {p q : ℕ}
    (hpq : (ComplexShape.up ℕ).Rel p q) :
    stepComponent f n p ≫ (stage f (n + 1)).d p q =
      (stage f n).d p q ≫ stepComponent f n q := sorry

/-- Lemma 15.29.6 (Stacks `0913`): the cochain map between consecutive stages. -/
@[stacks 0913 "powered Koszul direct transition"]
noncomputable def step (f : Fin r → R) (n : ℕ) :
    stage f n ⟶ stage f (n + 1) :=
  { f := stepComponent f n
    comm' := fun _ _ hpq ↦ stepComponent_comm f n hpq }

/-- Lemma 15.29.6 (Stacks `0913`): the sequential `ℕ`-indexed direct system of stages. -/
@[stacks 0913 "powered Koszul cochain direct system"]
noncomputable def system (f : Fin r → R) :
    ℕ ⥤ CochainComplex (ModuleCat R) ℕ :=
  Functor.ofSequence (step f)

/-! ### The comparison cocone -/

/-- The arrow whose Cech conerve supplies the positive degrees of the extended complex. -/
@[stacks 0913 "localization arrow for the extended Cech complex"]
noncomputable abbrev ringArrow (f : Fin r → R) : Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap R f))

/-- The positive-degree term of the Cech conerve. -/
@[stacks 0913 "positive-degree Cech conerve term"]
noncomputable abbrev cechTerm (f : Fin r → R) (p : ℕ) : ModuleCat R :=
  (ringArrow f).cechConerve.obj (SimplexCategory.mk p)

/-- The exponent appearing in one branch of the stage-to-Cech comparison. -/
@[stacks 0913 "branch exponent in the stage-to-Cech comparison"]
noncomputable def branchNumerator (f : Fin r → R) (n p : ℕ)
    (s : powersetCard (Fin r) p) (k : Fin p) : R :=
  Finset.prod (Finset.univ.erase k)
    (fun l ↦ f (powersetCard.ofFinEmbEquiv.symm s l) ^ (n + 1))

/-- A power of a family member is an allowed denominator for its principal localization. -/
@[stacks 0913 "principal-power denominator membership"]
theorem branchDenominator_mem (f : Fin r → R) (n : ℕ) (i : Fin r) :
    f i ^ (n + 1) ∈ Submonoid.powers (f i) := sorry

/-- Equal family indices transport the principal-power denominator membership. -/
@[stacks 0913 "principal-power denominator transport"]
theorem branchDenominator_mem_of_eq (f : Fin r → R) (n : ℕ) {i j : Fin r}
    (h : i = j) :
    f j ^ (n + 1) ∈ Submonoid.powers (f i) := sorry

/-- The localized branch vector used on an exterior basis generator. -/
@[stacks 0913 "localized branch vector of the Cech comparison"]
noncomputable def branchVector (f : Fin r → R) (n p : ℕ)
    (s : powersetCard (Fin r) p) (k : Fin p) :
    ∀ i : Fin r, LocalizedModule.Away (f i) R :=
  fun i ↦
    dite (i = powersetCard.ofFinEmbEquiv.symm s k)
      (fun h ↦
        LocalizedModule.mk (branchNumerator f n p s k)
          ⟨f (powersetCard.ofFinEmbEquiv.symm s k) ^ (n + 1),
            branchDenominator_mem_of_eq f n h⟩)
      (fun _ ↦ 0)

/-- The canonical coprojection from a localization factor into a Cech-conerve degree. -/
@[stacks 0913 "Cech branch coprojection"]
noncomputable abbrev cechBranchHom (f : Fin r → R) (p : ℕ) (k : Fin (p + 1)) :
    ModuleCat.of R (∀ i : Fin r, LocalizedModule.Away (f i) R) ⟶ cechTerm f p :=
  CategoryTheory.Arrow.cechConerve.ι (ringArrow f) (SimplexCategory.mk p) k

/-- A complementary subset of a basis index. -/
@[stacks 0913 "complementary subset cardinality"]
theorem complement_card_eq (p : ℕ) (hp : p ≤ r) :
    p + (r - p) = Fintype.card (Fin r) := sorry

/-- The complement of an `(r - p)`-subset, viewed as a `p`-subset. -/
@[stacks 0913 "complementary subset index"]
noncomputable def complementSubset (p : ℕ) (hp : p ≤ r)
    (s : powersetCard (Fin r) (r - p)) : powersetCard (Fin r) p :=
  powersetCard.compl (complement_card_eq (r := r) p hp) s

/-- The image of an exterior basis vector in the positive Cech degree. -/
@[stacks 0913 "image of an exterior basis vector in Cech degree"]
noncomputable def alternatingBasisImage (f : Fin r → R) (n p : ℕ) (hp : p + 1 ≤ r)
    (s : powersetCard (Fin r) (r - (p + 1))) : cechTerm f p :=
  let t := complementSubset (r := r) (p + 1) hp s
  ∑ k : Fin (p + 1),
    (-1 : ℤ) ^ (k : ℕ) •
      (cechBranchHom f p k).hom (branchVector f n (p + 1) t k)

/-- The linear map on positive degrees in the comparison cocone. -/
@[stacks 0913 "positive-degree map in the Koszul-Cech comparison"]
noncomputable def alternatingMap (f : Fin r → R) (n p : ℕ) (hp : p + 1 ≤ r) :
    ⋀[R]^(r - (p + 1)) (Fin r → R) →ₗ[R] cechTerm f p :=
  (exteriorBasis (r - (p + 1))).constr R (alternatingBasisImage f n p hp)

/-- The top exterior-degree augmentation used in cochain degree zero. -/
@[stacks 0913 "degree-zero augmentation in the Koszul-Cech comparison"]
noncomputable def degreeZeroMap :
    ⋀[R]^r (Fin r → R) →ₗ[R] R :=
  (exteriorBasis r).constr R (fun _ ↦ (1 : R))

/-- The degree-zero object of the extended alternating Cech complex. -/
@[stacks 0913 "extended Cech degree zero identification"]
theorem extended_X_zero (f : Fin r → R) :
    (LocalizedModule.Away.Cech.Alternating.extended f R).X 0 = ModuleCat.of R R := sorry

/-- The positive-degree objects of the extended alternating Cech complex. -/
@[stacks 0913 "extended Cech positive-degree identification"]
theorem extended_X_succ (f : Fin r → R) (p : ℕ) :
    (LocalizedModule.Away.Cech.Alternating.extended f R).X (p + 1) = cechTerm f p := sorry

/-- The component of the explicit stage-to-Cech comparison map. -/
@[stacks 0913 "component of the powered Koszul-Cech comparison"]
noncomputable def comparisonComponent (f : Fin r → R) (n p : ℕ) :
    (stage f n).X p ⟶
      (LocalizedModule.Away.Cech.Alternating.extended f R).X p :=
  if hp : p ≤ r then
    match p with
    | 0 =>
        (stageIso f n 0 hp).hom ≫ ModuleCat.ofHom degreeZeroMap ≫
          eqToHom (extended_X_zero f).symm
    | q + 1 =>
        (stageIso f n (q + 1) hp).hom ≫
          ModuleCat.ofHom (alternatingMap f n q hp) ≫
          eqToHom (extended_X_succ f q).symm
  else
    0

/-- The stage-to-Cech comparison map is compatible with the differentials. -/
@[stacks 0913 "stage-to-Cech comparison commutativity"]
theorem comparisonComponent_comm (f : Fin r → R) (n : ℕ) {p q : ℕ}
    (hpq : (ComplexShape.up ℕ).Rel p q) :
    comparisonComponent f n p ≫
        (LocalizedModule.Away.Cech.Alternating.extended f R).d p q =
      (stage f n).d p q ≫ comparisonComponent f n q := sorry

/-- Lemma 15.29.6 (Stacks `0913`): the explicit map from a powered stage to the extended Cech
complex. -/
@[stacks 0913 "powered stage to extended Cech comparison"]
noncomputable def comparison (f : Fin r → R) (n : ℕ) :
    stage f n ⟶ LocalizedModule.Away.Cech.Alternating.extended f R :=
  { f := comparisonComponent f n
    comm' := fun _ _ hpq ↦ comparisonComponent_comm f n hpq }

/-- Naturality of the explicit comparison with respect to the direct transition. -/
@[stacks 0913 "comparison cocone naturality"]
theorem comparison_naturality (f : Fin r → R) (n : ℕ) :
    step f n ≫ comparison f (n + 1) = comparison f n := sorry

/-- Naturality in the form expected by the constant-target comparison cocone. -/
@[stacks 0913 "comparison cocone naturality with constant target"]
theorem cocone_naturality (f : Fin r → R) (n : ℕ) :
    (system f).map (homOfLE (n.le_add_right 1)) ≫ comparison f (n + 1) =
      comparison f n ≫
        ((Functor.const ℕ).obj
          (LocalizedModule.Away.Cech.Alternating.extended f R)).map
            (homOfLE (n.le_add_right 1)) := sorry

/-- The explicit cocone from the powered Koszul direct system to the extended Cech complex. -/
@[stacks 0913 "powered Koszul comparison cocone"]
noncomputable def cocone (f : Fin r → R) :
    Cocone (system f) where
  pt := LocalizedModule.Away.Cech.Alternating.extended f R
  ι := NatTrans.ofSequence
    (fun n ↦ comparison f n)
    (cocone_naturality f)

/-- The induced map from the colimit of powered Koszul stages to the extended Cech complex. -/
@[stacks 0913 "colimit comparison morphism"]
noncomputable def colimitComparison (f : Fin r → R) :
    colimit (system f) ⟶ LocalizedModule.Away.Cech.Alternating.extended f R :=
  colimit.desc _ (cocone f)

/-- The degreewise comparison is an isomorphism; this is the localization calculation in the
source proof. -/
@[stacks 0913 "degreewise colimit comparison isomorphism"]
theorem colimitComparison_component_isIso (f : Fin r → R) (p : ℕ) :
    IsIso ((colimitComparison f).f p) := sorry

/-- The colimit comparison is an isomorphism of cochain complexes. -/
@[stacks 0913 "colimit comparison isomorphism"]
theorem colimitComparison_isIso (f : Fin r → R) :
    IsIso (colimitComparison f) := sorry

/-- The final isomorphism constructor with the colimit comparison proof supplied explicitly. -/
@[stacks 0913 "powered Koszul colimit isomorphism proof gate"]
noncomputable def extendedIsoOf (f : Fin r → R)
    (h : IsIso (colimitComparison f)) :
    LocalizedModule.Away.Cech.Alternating.extended f R ≅ colimit (system f) :=
  letI := h
  (asIso (colimitComparison f)).symm

/-- The inverse of the proof-gated colimit isomorphism is the explicit colimit comparison. -/
@[stacks 0913 "powered Koszul colimit isomorphism inverse"]
theorem extendedIsoOf_inv (f : Fin r → R) (h : IsIso (colimitComparison f)) :
    (extendedIsoOf f h).inv = colimitComparison f := sorry

/-- Lemma 15.29.6 (Stacks `0913`): the extended alternating Cech complex is the colimit of the
powered Koszul direct system. -/
@[stacks 0913 "extended Cech colimit of powered Koszul stages"]
noncomputable def extendedIso (f : Fin r → R) :
    LocalizedModule.Away.Cech.Alternating.extended f R ≅ colimit (system f) :=
  extendedIsoOf f (colimitComparison_isIso f)

/-- The inverse of the canonical extended-Cech/Koszul-colimit isomorphism is the explicit
comparison morphism. -/
@[stacks 0913 "extended Cech colimit isomorphism inverse"]
theorem extendedIso_inv (f : Fin r → R) :
    (extendedIso f).inv = colimitComparison f := sorry

end LocalizedModule.Away.Cech.Koszul

end
