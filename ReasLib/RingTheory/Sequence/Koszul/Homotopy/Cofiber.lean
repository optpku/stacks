/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.Extend
public import ReasLib.Algebra.Homology.Homotopy.CofiberScalarMul
public import ReasLib.RingTheory.Sequence.Koszul.Family
public import ReasLib.RingTheory.Sequence.Koszul.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes and homotopy cofibers of products

Adjoining a scalar to a linear form turns the product-scalar cofiber comparison into the
corresponding comparison for Koszul complexes. The same statement is exposed for finite families.

@stack 0628
@stack 0629
@stack 062B
@stack 062C
-/

@[expose] public section

open CategoryTheory ComplexShape Limits HomologicalComplex ModuleCat exteriorPower
open HomologicalComplex.homotopyCofiber

noncomputable section

universe u

namespace KoszulComplex

variable {R : Type u} [CommRing R]

namespace Cofiber

variable {E : Type u} [AddCommGroup E] [Module R E]

/-- The degree-`n + 1` split map from the exterior power of `E × R` to the two summands of the
scalar homotopy cofiber. -/
@[stacks 0628 "forward exterior-power splitting"]
noncomputable def succSplitHom (n : ℕ) :
    (ModuleCat.of R (E × R)).exteriorPower (n + 1) ⟶
      (ModuleCat.of R E).exteriorPower n ⊞ (ModuleCat.of R E).exteriorPower (n + 1) :=
  biprod.lift
    (ModuleCat.ofHom (koszulDifferentialLinearMap (LinearMap.snd R E R) n) ≫
      ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.fst R E R)) n)
    (ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.fst R E R)) (n + 1))

/-- The inverse degree-`n + 1` split map, using the left wedge with `(0, 1)` on the lower
summand. -/
@[stacks 0628 "inverse exterior-power splitting"]
noncomputable def succSplitInv (n : ℕ) :
    (ModuleCat.of R E).exteriorPower n ⊞ (ModuleCat.of R E).exteriorPower (n + 1) ⟶
      (ModuleCat.of R (E × R)).exteriorPower (n + 1) :=
  biprod.desc
    (ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.inl R E R)) n ≫
      ModuleCat.ofHom (koszulLeftWedge ((0 : E), (1 : R)) n))
    (ModuleCat.exteriorPower.map (ModuleCat.ofHom (LinearMap.inl R E R)) (n + 1))

/-- The inverse split followed by the forward split is the identity. -/
theorem succSplitInv_hom_id (n : ℕ) :
    succSplitInv (R := R) (E := E) n ≫ succSplitHom (R := R) (E := E) n = 𝟙 _ := sorry

/-- The forward split followed by the inverse split is the identity. -/
theorem succSplitHom_inv_id (n : ℕ) :
    succSplitHom (R := R) (E := E) n ≫ succSplitInv (R := R) (E := E) n = 𝟙 _ := sorry

/-- The canonical degree-`n + 1` decomposition of the exterior power of `E × R`. -/
@[stacks 0628 "exterior-power splitting isomorphism"]
noncomputable def succSplitIso (n : ℕ) :
    (ModuleCat.of R (E × R)).exteriorPower (n + 1) ≅
      (ModuleCat.of R E).exteriorPower n ⊞ (ModuleCat.of R E).exteriorPower (n + 1) :=
  (LinearEquiv.ofLinear
    (succSplitHom (R := R) (E := E) n).hom
    (succSplitInv (R := R) (E := E) n).hom
    (congrArg ModuleCat.Hom.hom (succSplitInv_hom_id (R := R) (E := E) n))
    (congrArg ModuleCat.Hom.hom (succSplitHom_inv_id (R := R) (E := E) n))).toModuleIso

/-- Degree zero has no predecessor in the downward complex shape. -/
theorem not_rel_zero_next : ¬(ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := sorry

/-- The successor degree is related to its predecessor in the downward complex shape. -/
theorem rel_succ (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n := sorry

/-- The degreewise comparison between the Koszul complex of an adjoined scalar and the scalar
homotopy cofiber. -/
@[stacks 0628 "degreewise Koszul-cofiber comparison"]
noncomputable def componentIso (φ : E →ₗ[R] R) (f : R) (n : ℕ) :
    (koszulComplex (koszulCoprodScalarLinearMap φ f)).X n ≅
      (homotopyCofiber (f • 𝟙 (koszulComplex φ))).X n :=
  let α := f • 𝟙 (koszulComplex φ)
  match n with
  | 0 =>
      ModuleCat.exteriorPower.iso₀ (ModuleCat.of R (E × R)) ≪≫
        (ModuleCat.exteriorPower.iso₀ (ModuleCat.of R E)).symm ≪≫
        (XIso α 0 not_rel_zero_next).symm
  | n + 1 =>
      succSplitIso n ≪≫
        (XIsoBiprod α (n + 1) n (rel_succ n)).symm

/-- The degreewise comparison commutes with the Koszul and homotopy-cofiber differentials. -/
theorem componentIso_commSq (φ : E →ₗ[R] R) (f : R) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    CommSq
      (componentIso φ f i).hom
      ((koszulComplex (koszulCoprodScalarLinearMap φ f)).d i j)
      ((homotopyCofiber (f • 𝟙 (koszulComplex φ))).d i j)
      (componentIso φ f j).hom := sorry

/-- Lemma 15.28.7: adjoining multiplication by `f` to a linear form identifies its Koszul
complex with the homotopy cofiber of multiplication by `f` on the original Koszul complex. -/
@[stacks 0628 "Lemma 15.28.7"]
noncomputable def coprodScalarIso (φ : E →ₗ[R] R) (f : R) :
    koszulComplex (koszulCoprodScalarLinearMap φ f) ≅
      homotopyCofiber (f • 𝟙 (koszulComplex φ)) :=
  Hom.isoOfComponents (componentIso φ f)
    (fun i j hij ↦ (componentIso_commSq φ f i j hij).w)

end Cofiber

namespace Family

/-- The canonical linear equivalence splitting the final coordinate from a vector indexed by
`Fin (r + 1)`. -/
@[stacks 0629 "splitting the last coordinate of a finite family"]
noncomputable def snocLinearEquiv (r : ℕ) :
    ((Fin r → R) × R) ≃ₗ[R] (Fin (r + 1) → R) :=
  ((LinearEquiv.piCongrLeft R (fun _ : Option (Fin r) ↦ R) finSuccEquivLast) ≪≫ₗ
      LinearEquiv.piOptionEquivProd R ≪≫ₗ
      LinearEquiv.prodComm R R (Fin r → R)).symm

/-- The finite-family linear form agrees with the coproduct-scalar form after applying the
inverse final-coordinate split. -/
theorem linearForm_snoc_comp_symm {r : ℕ} (fs : Fin r → R) (a : R) :
    (koszulCoprodScalarLinearMap (koszulLinearForm fs) a).comp
        (snocLinearEquiv r).symm.toLinearMap =
      koszulLinearForm (Fin.snoc fs a) := sorry

/-- The finite-family linear form agrees with the coproduct-scalar form after applying the
forward final-coordinate split. -/
theorem linearForm_snoc_comp {r : ℕ} (fs : Fin r → R) (a : R) :
    (koszulLinearForm (Fin.snoc fs a)).comp (snocLinearEquiv r).toLinearMap =
      koszulCoprodScalarLinearMap (koszulLinearForm fs) a := sorry

/-- The forward Koszul map from a snoc family to its coproduct-scalar presentation. -/
@[stacks 0629 "forward snoc-family Koszul map"]
noncomputable def snocCoprodHom {r : ℕ} (fs : Fin r → R) (a : R) :
    family (Fin.snoc fs a) ⟶ koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a) :=
  KoszulComplex.map (snocLinearEquiv r).symm.toLinearMap (linearForm_snoc_comp_symm fs a)

/-- The inverse Koszul map from the coproduct-scalar presentation to a snoc family. -/
@[stacks 0629 "inverse snoc-family Koszul map"]
noncomputable def snocCoprodInv {r : ℕ} (fs : Fin r → R) (a : R) :
    koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a) ⟶
      family (Fin.snoc fs a) :=
  KoszulComplex.map (snocLinearEquiv r).toLinearMap (linearForm_snoc_comp fs a)

/-- The snoc-to-coproduct map followed by its inverse is the identity. -/
theorem snocCoprodHom_inv_id {r : ℕ} (fs : Fin r → R) (a : R) :
    snocCoprodHom fs a ≫ snocCoprodInv fs a = 𝟙 (family (Fin.snoc fs a)) := sorry

/-- The coproduct-to-snoc map followed by its inverse is the identity. -/
theorem snocCoprodInv_hom_id {r : ℕ} (fs : Fin r → R) (a : R) :
    snocCoprodInv fs a ≫ snocCoprodHom fs a =
      𝟙 (koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a)) := sorry

/-- The Koszul complex of a snoc family is canonically isomorphic to the coproduct-scalar
presentation of its final member. -/
@[stacks 0629 "snoc-family Koszul isomorphism"]
noncomputable def snocCoprodIso {r : ℕ} (fs : Fin r → R) (a : R) :
    family (Fin.snoc fs a) ≅ koszulComplex (koszulCoprodScalarLinearMap (koszulLinearForm fs) a) :=
  CategoryTheory.Iso.mk (snocCoprodHom fs a) (snocCoprodInv fs a)
    (snocCoprodHom_inv_id fs a) (snocCoprodInv_hom_id fs a)

/-- Lemma 15.28.8: a finite-family Koszul complex is canonically isomorphic to the homotopy
cofiber of multiplication by its final entry on the Koszul complex of the truncated family. -/
@[stacks 0629 "Lemma 15.28.8"]
noncomputable def truncateLastIsoCofiber {r : ℕ} (f : Fin (r + 1) → R) :
    family f ≅ homotopyCofiber ((f (Fin.last r)) • 𝟙 (family (Fin.init f))) :=
  eqToIso (congrArg family (Fin.snoc_init_self f)).symm ≪≫
    snocCoprodIso (Fin.init f) (f (Fin.last r)) ≪≫
    Cofiber.coprodScalarIso (koszulLinearForm (Fin.init f)) (f (Fin.last r))

end Family

/-- Lemma 15.28.10: after adjoining scalar multiplication by `f`, `g`, and `f * g` to a linear
form `φ`, the Koszul complex for `f * g` is homotopy equivalent to the cofiber of a map from the
degree-one shift of the `f`-complex to the `g`-complex. -/
@[stacks 062B "Lemma 15.28.10"]
theorem coprodScalarMul_exists_homotopyEquiv {E : Type u} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ α :
        (((koszulComplex (koszulCoprodScalarLinearMap φ f)).extend embeddingDownNat)⟦
          (-1 : ℤ)⟧).restriction embeddingDownNat ⟶
          koszulComplex (koszulCoprodScalarLinearMap φ g),
      Nonempty
        (HomotopyEquiv
          (koszulComplex (koszulCoprodScalarLinearMap φ (f * g)))
          (homotopyCofiber α)) := sorry

namespace Family

/-- Lemma 15.28.11: for a finite family `fs`, the Koszul complex on
`Fin.snoc fs (f * g)` is homotopy equivalent to the cofiber of a map from the degree-one shift
of the complex on `Fin.snoc fs f` to the complex on `Fin.snoc fs g`. -/
@[stacks 062C "Lemma 15.28.11"]
theorem snocMul_exists_homotopyEquiv {r : ℕ} (fs : Fin r → R) (f g : R) :
    ∃ α :
        (((family (Fin.snoc fs f)).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction
            embeddingDownNat ⟶ family (Fin.snoc fs g),
      Nonempty
        (HomotopyEquiv (family (Fin.snoc fs (f * g))) (homotopyCofiber α)) := sorry

end Family
end KoszulComplex
