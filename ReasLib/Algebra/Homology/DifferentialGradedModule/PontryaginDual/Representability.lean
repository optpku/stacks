/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Shift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual.Right

/-!
# Representability by the dual regular module

The enriched Hom complex `Hom_A(M, Aᵛ)` is canonically the Pontryagin dual complex `Mᵛ`.
Combining this comparison with the generic shifted-Hom API identifies ordinary morphisms with
cycles and homotopy-category morphisms with homology.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.PontryaginRepresentable

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Evaluate a homogeneous map `M ⟶ Aᵛ` on the unit of `A`. -/
@[stacks 09K4 "unit evaluation from the enriched Hom component"]
def characterOfGradedHom (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : GradedHom A M A.dualRegularModule k) : CharacterModule (M.X (-k)) :=
  (AddMonoidHom.eval A.one).comp
    (ModuleCat.castLinearMap
      ((congrArg A.dualRegularModule.X (neg_add_cancel k)).trans rfl)
      (f (-k))).toAddMonoidHom

/-- Unit evaluation is additive in the homogeneous map. -/
theorem characterOfGradedHom_add (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f g : GradedHom A M A.dualRegularModule k) :
    characterOfGradedHom M k (f + g) =
      characterOfGradedHom M k f + characterOfGradedHom M k g := sorry

/-- Unit evaluation is linear in the homogeneous map. -/
theorem characterOfGradedHom_smul (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (r : R) (f : GradedHom A M A.dualRegularModule k) :
    characterOfGradedHom M k (r • f) = r • characterOfGradedHom M k f := sorry

/-- Unit evaluation as a linear map from the enriched Hom component to the character module. -/
@[stacks 09K4 "linear unit evaluation into the character module"]
def toCharacter (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    GradedHom A M A.dualRegularModule k →ₗ[R] CharacterModule (M.X (-k)) where
  toFun := characterOfGradedHom M k
  map_add' := characterOfGradedHom_add M k
  map_smul' := characterOfGradedHom_smul M k

/-- A character of `M^{-k}` paired with the right action of `A`. -/
@[stacks 09K4 "right-action pairing of a character with a homogeneous element"]
def pairingValue (M : DifferentialGradedModule.{u, v} A) (k n : ℤ)
    (c : CharacterModule (M.X (-k))) (x : M.X n) :
    CharacterModule (A.X (-(n + k))) :=
  CharacterModule.dual
    (ModuleCat.castLinearMap
      (congrArg M.X
        ((congrArg (fun z : ℤ ↦ n + z) (Int.neg_add (a := n) (b := k))).trans
          (add_neg_cancel_left n (-k))))
      (M.smul n (-(n + k)) x)) c

/-- The action pairing is additive in the module variable. -/
theorem pairingValue_add (M : DifferentialGradedModule.{u, v} A) (k n : ℤ)
    (c : CharacterModule (M.X (-k))) (x y : M.X n) :
    pairingValue M k n c (x + y) = pairingValue M k n c x + pairingValue M k n c y := sorry

/-- The action pairing is linear in the module variable. -/
theorem pairingValue_smul (M : DifferentialGradedModule.{u, v} A) (k n : ℤ)
    (c : CharacterModule (M.X (-k))) (r : R) (x : M.X n) :
    pairingValue M k n c (r • x) = r • pairingValue M k n c x := sorry

/-- A character of `M^{-k}` induces the degree-`n` component of an `A`-linear homogeneous map
to `Aᵛ`. -/
@[stacks 09K4 "degreewise action pairing as a linear map"]
def pairingHom (M : DifferentialGradedModule.{u, v} A) (k n : ℤ)
    (c : CharacterModule (M.X (-k))) :
    M.X n →ₗ[R] CharacterModule (A.X (-(n + k))) where
  toFun := pairingValue M k n c
  map_add' := pairingValue_add M k n c
  map_smul' := pairingValue_smul M k n c

/-- A character of `M^{-k}` extends along the right `A`-action to a homogeneous `A`-linear map
`M ⟶ Aᵛ` of degree `k`. -/
@[stacks 09K4 "extension of a character to a homogeneous enriched Hom map"]
def gradedHomOfCharacter (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (c : CharacterModule (M.X (-k))) : GradedHom A M A.dualRegularModule k :=
  ⟨fun n ↦ ModuleCat.castLinearMap rfl (pairingHom M k n c),
    sorry⟩

/-- Extension along the action is additive in the character. -/
theorem gradedHomOfCharacter_add (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (c d : CharacterModule (M.X (-k))) :
    gradedHomOfCharacter M k (c + d) =
      gradedHomOfCharacter M k c + gradedHomOfCharacter M k d := sorry

/-- Extension along the action is linear in the character. -/
theorem gradedHomOfCharacter_smul (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (r : R) (c : CharacterModule (M.X (-k))) :
    gradedHomOfCharacter M k (r • c) = r • gradedHomOfCharacter M k c := sorry

/-- Extension along the action as a linear map into the enriched Hom component. -/
@[stacks 09K4 "linear extension from characters to the enriched Hom component"]
def fromCharacter (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    CharacterModule (M.X (-k)) →ₗ[R] GradedHom A M A.dualRegularModule k where
  toFun := gradedHomOfCharacter M k
  map_add' := gradedHomOfCharacter_add M k
  map_smul' := gradedHomOfCharacter_smul M k

/-- Unit evaluation identifies the degree-`k` enriched Hom component with characters of
`M^{-k}`. -/
@[stacks 09K4 "degreewise enriched Hom-character equivalence"]
def gradedHomEquivCharacter (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    GradedHom A M A.dualRegularModule k ≃ₗ[R] CharacterModule (M.X (-k)) where
  toLinearMap := toCharacter M k
  invFun := fromCharacter M k
  left_inv := sorry
  right_inv := sorry

/-- Evaluation on the unit defines a cochain map `Hom_A(M, Aᵛ) ⟶ Mᵛ`. -/
@[stacks 09K4 "enriched Hom to Pontryagin-dual cochain map"]
def homComplexToDual (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedCategory.homComplex M A.dualRegularModule ⟶
      M.pontryaginDual.toCochainComplex where
  f k := ModuleCat.ofHom (gradedHomEquivCharacter M k).toLinearMap
  comm' := sorry

/-- Extension along the right action defines the inverse cochain map `Mᵛ ⟶ Hom_A(M, Aᵛ)`. -/
@[stacks 09K4 "Pontryagin-dual to enriched Hom cochain map"]
def dualToHomComplex (M : DifferentialGradedModule.{u, v} A) :
    M.pontryaginDual.toCochainComplex ⟶
      DifferentialGradedCategory.homComplex M A.dualRegularModule where
  f k := ModuleCat.ofHom (gradedHomEquivCharacter M k).symm.toLinearMap
  comm' := sorry

/-- The forward cochain comparison is degreewise unit evaluation. -/
@[simp, stacks 09K4 "component of the enriched Hom to Pontryagin-dual map"]
theorem homComplexToDual_f (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (homComplexToDual M).f k =
      ModuleCat.ofHom (gradedHomEquivCharacter M k).toLinearMap := sorry

/-- The inverse cochain comparison is degreewise extension along the right action. -/
@[simp, stacks 09K4 "component of the Pontryagin-dual to enriched Hom map"]
theorem dualToHomComplex_f (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (dualToHomComplex M).f k =
      ModuleCat.ofHom (gradedHomEquivCharacter M k).symm.toLinearMap := sorry

/-- Lemma 22.19.3 (09K4), enriched core: evaluation on the unit identifies
`Hom_A(M, Aᵛ)` with the Pontryagin dual complex `Mᵛ`. -/
@[stacks 09K4 "internal Hom into the dual regular module"]
def homComplexIsoDual (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedCategory.homComplex M A.dualRegularModule ≅
      M.pontryaginDual.toCochainComplex where
  hom := homComplexToDual M
  inv := dualToHomComplex M
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The Hom-complex comparison induces an isomorphism on degree-`k` cycles. -/
@[stacks 09K4 "cycle-level Hom-complex and Pontryagin-dual isomorphism"]
def cyclesIsoDual (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (DifferentialGradedCategory.homComplex M A.dualRegularModule).cycles k ≅
      M.pontryaginDual.cycles k :=
  HomologicalComplex.cyclesMapIso (homComplexIsoDual M) k

/-- The Hom-complex comparison induces an isomorphism on degree-`k` homology. -/
@[stacks 09K4 "homology-level Hom-complex and Pontryagin-dual isomorphism"]
def homologyIsoDual (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (DifferentialGradedCategory.homComplex M A.dualRegularModule).homology k ≅
      M.pontryaginDual.homology k :=
  HomologicalComplex.homologyMapIso (homComplexIsoDual M) k

/-- DG-module morphisms `M ⟶ Aᵛ[k]` are canonically the degree-`k` cycles of the Pontryagin
dual complex `Mᵛ`, linearly over `R`. -/
@[stacks 09K4]
noncomputable def homLinearEquivDualCycles
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (M ⟶ Aᵛ[k]) ≃ₗ[R] M.pontryaginDual.cycles k :=
  (Homotopy.shiftHomLinearEquivCycles M A.dualRegularModule k).trans
    (cyclesIsoDual M k).toLinearEquiv

/-- Lemma 22.19.3 (1) (09K4), unbundled form: DG-module morphisms `M ⟶ Aᵛ[k]` are
canonically the degree-`k` cycles of `Mᵛ`. -/
@[stacks 09K4]
def homEquivDualCycles (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (M ⟶ Aᵛ[k]) ≃ M.pontryaginDual.cycles k :=
  (homLinearEquivDualCycles M k).toEquiv

/-- Homotopy-category morphisms `M ⟶ Aᵛ[k]` are canonically the degree-`k` homology of the
Pontryagin dual complex `Mᵛ`, linearly over `R`. -/
@[stacks 09K4]
noncomputable def homotopyLinearEquivDualHomology
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ((toK A).obj M ⟶ (toK A).obj Aᵛ[k]) ≃ₗ[R] M.pontryaginDual.homology k :=
  (Homotopy.shiftHomotopyLinearEquivHomology M A.dualRegularModule k).trans
    (homologyIsoDual M k).toLinearEquiv

/-- Lemma 22.19.3 (2) (09K4), unbundled form: homotopy-category morphisms `M ⟶ Aᵛ[k]`
are canonically the degree-`k` homology of `Mᵛ`. -/
@[stacks 09K4]
def homotopyEquivDualHomology (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    ((toK A).obj M ⟶ (toK A).obj Aᵛ[k]) ≃ M.pontryaginDual.homology k :=
  (homotopyLinearEquivDualHomology M k).toEquiv

end DifferentialGradedModule.PontryaginRepresentable
