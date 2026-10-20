module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.ResidueMap

/-!
# Completed tensor product in `CompleteLocalAlgCat`

The coproduct of `R` and `S` in `Ĉ_Λ` is the adic completion of `R.carrier ⊗[Λ] S.carrier`
at the kernel of the canonical map to `k` induced by the two residue identifications.
-/

@[expose] public section

open CategoryTheory IsLocalRing Algebra.TensorProduct
open CategoryTheory.Limits (BinaryCofan HasColimit HasBinaryCoproducts pair ColimitCocone IsColimit)
open scoped TensorProduct

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

noncomputable section

/-- The distinguished maximal ideal `m` of `R.carrier ⊗[Λ] S.carrier` is the kernel of the
canonical map to `k`. -/
def tensorAdicIdeal (R S : CompleteLocalAlgCat Λ k) :
    Ideal (R.carrier ⊗[Λ] S.carrier) :=
  RingHom.ker (productMap (residueFieldHom R) (residueFieldHom S)).toRingHom

/-- The canonical map `R.carrier ⊗[Λ] S.carrier →ₐ[Λ] k` is surjective. -/
theorem residueFieldHom_productMap_surjective (R S : CompleteLocalAlgCat Λ k) :
    Function.Surjective (productMap (residueFieldHom R) (residueFieldHom S)) := sorry

/-- The kernel of the canonical map to `k` is a maximal ideal. -/
theorem tensorAdicIdeal_isMaximal (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicIdeal R S).IsMaximal := sorry

/-- The kernel of the canonical map to `k` is a maximal ideal. -/
instance instTensorAdicIdealIsMaximal (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicIdeal R S).IsMaximal :=
  tensorAdicIdeal_isMaximal R S

/-- The kernel of the canonical map to `k` is finitely generated. -/
theorem tensorAdicIdeal_fg (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicIdeal R S).FG := sorry

/-- The completed tensor is a local ring. -/
instance instTensorAdicCompletionIsLocalRing (R S : CompleteLocalAlgCat Λ k) :
    IsLocalRing (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier)) := sorry

/-- The completed tensor is a Noetherian ring. -/
instance instTensorAdicCompletionIsNoetherianRing (R S : CompleteLocalAlgCat Λ k) :
    IsNoetherianRing
      (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier)) := sorry

/-- The completed tensor is a complete local ring. -/
instance instTensorAdicCompletionIsCompleteLocalRing (R S : CompleteLocalAlgCat Λ k) :
    IsCompleteLocalRing
      (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier)) := sorry

/-- Scalar tower for the algebra map from the uncompleted tensor into its adic completion. -/
instance instTensorAdicCompletionIsScalarTower (R S : CompleteLocalAlgCat Λ k) :
    IsScalarTower Λ (R.carrier ⊗[Λ] S.carrier)
      (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier)) := sorry

/-- The maximal ideal of the completed tensor is the extension of `tensorAdicIdeal`. -/
theorem tensorAdicCompletion_maximalIdeal_eq (R S : CompleteLocalAlgCat Λ k) :
    IsLocalRing.maximalIdeal (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier)) =
      (tensorAdicIdeal R S).map
        (algebraMap (R.carrier ⊗[Λ] S.carrier)
          (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier))) := sorry

/-- Residue identification of the completed tensor with `k`. -/
def tensorAdicCompletionResidueFieldIso (R S : CompleteLocalAlgCat Λ k) :
    ResidueField (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier)) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ (tensorAdicCompletion_maximalIdeal_eq R S)).trans
    (((AdicCompletion.quotientExtensionEquiv (tensorAdicIdeal R S)
          (tensorAdicIdeal_fg R S)).restrictScalars Λ).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (residueFieldHom_productMap_surjective R S)))

/-- The `m`-adic completion of `R.carrier ⊗[Λ] S.carrier`, as an object of `Ĉ_Λ`. -/
def tensorAdicCompletion (R S : CompleteLocalAlgCat Λ k) : CompleteLocalAlgCat Λ k :=
  of (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier))
    (tensorAdicCompletionResidueFieldIso R S)

/-- The carrier of the completed tensor is the indicated adic completion. -/
theorem tensorAdicCompletion_carrier (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicCompletion R S).carrier =
      AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier) := sorry

/-- The bundled residue identification of the completed tensor is the constructed equivalence. -/
theorem tensorAdicCompletion_residueFieldIso (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicCompletion R S).residueFieldIso =
      tensorAdicCompletionResidueFieldIso R S := sorry

/-- The left tensor inclusion followed by the canonical adic completion map. -/
def tensorAdicCompletionInlHom (R S : CompleteLocalAlgCat Λ k) :
    R.carrier →ₐ[Λ] (tensorAdicCompletion R S).carrier :=
  (IsScalarTower.toAlgHom Λ (R.carrier ⊗[Λ] S.carrier)
      (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier))).comp
    (includeLeft : R.carrier →ₐ[Λ] R.carrier ⊗[Λ] S.carrier)

/-- The left inclusion into the completed tensor is a local algebra homomorphism. -/
theorem tensorAdicCompletionInl_isLocalHom (R S : CompleteLocalAlgCat Λ k) :
    IsLocalHom (tensorAdicCompletionInlHom R S) := sorry

/-- The left inclusion preserves the chosen residue-field identifications. -/
theorem tensorAdicCompletionInl_residue_compat (R S : CompleteLocalAlgCat Λ k) :
    residueCompat (tensorAdicCompletionInlHom R S)
        (tensorAdicCompletionInl_isLocalHom R S) = residueIsoHom R := sorry

/-- Coproduct inclusion of the first factor into the completed tensor. -/
def tensorAdicCompletionInl (R S : CompleteLocalAlgCat Λ k) :
    Hom R (tensorAdicCompletion R S) :=
  Hom.of (tensorAdicCompletionInlHom R S)
    (tensorAdicCompletionInl_isLocalHom R S) (tensorAdicCompletionInl_residue_compat R S)

/-- The right tensor inclusion followed by the canonical adic completion map. -/
def tensorAdicCompletionInrHom (R S : CompleteLocalAlgCat Λ k) :
    S.carrier →ₐ[Λ] (tensorAdicCompletion R S).carrier :=
  (IsScalarTower.toAlgHom Λ (R.carrier ⊗[Λ] S.carrier)
      (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier))).comp
    (includeRight : S.carrier →ₐ[Λ] R.carrier ⊗[Λ] S.carrier)

/-- The right inclusion into the completed tensor is a local algebra homomorphism. -/
theorem tensorAdicCompletionInr_isLocalHom (R S : CompleteLocalAlgCat Λ k) :
    IsLocalHom (tensorAdicCompletionInrHom R S) := sorry

/-- The right inclusion preserves the chosen residue-field identifications. -/
theorem tensorAdicCompletionInr_residue_compat (R S : CompleteLocalAlgCat Λ k) :
    residueCompat (tensorAdicCompletionInrHom R S)
        (tensorAdicCompletionInr_isLocalHom R S) = residueIsoHom S := sorry

/-- Coproduct inclusion of the second factor into the completed tensor. -/
def tensorAdicCompletionInr (R S : CompleteLocalAlgCat Λ k) :
    Hom S (tensorAdicCompletion R S) :=
  Hom.of (tensorAdicCompletionInrHom R S)
    (tensorAdicCompletionInr_isLocalHom R S) (tensorAdicCompletionInr_residue_compat R S)

/-- The underlying algebra map of the left inclusion is `includeLeft` then the completion map. -/
theorem tensorAdicCompletionInl_hom (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicCompletionInl R S).hom =
      (IsScalarTower.toAlgHom Λ (R.carrier ⊗[Λ] S.carrier)
            (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier))).comp
        (includeLeft : R.carrier →ₐ[Λ] R.carrier ⊗[Λ] S.carrier) := sorry

/-- The underlying algebra map of the right inclusion is `includeRight` then the completion map. -/
theorem tensorAdicCompletionInr_hom (R S : CompleteLocalAlgCat Λ k) :
    (tensorAdicCompletionInr R S).hom =
      (IsScalarTower.toAlgHom Λ (R.carrier ⊗[Λ] S.carrier)
            (AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier))).comp
        (includeRight : S.carrier →ₐ[Λ] R.carrier ⊗[Λ] S.carrier) := sorry

/-- The uncompleted coproduct map `R.carrier ⊗[Λ] S.carrier →ₐ[Λ] T.carrier`. -/
def tensorLift {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T) :
    R.carrier ⊗[Λ] S.carrier →ₐ[Λ] T.carrier :=
  productMap f.hom g.hom

/-- Powers of `tensorAdicIdeal` land in powers of the target maximal ideal. -/
theorem tensorLift_pow_eq_zero {R S T : CompleteLocalAlgCat Λ k}
    (f : Hom R T) (g : Hom S T) (n : ℕ) :
    ∀ a, a ∈ tensorAdicIdeal R S ^ n →
      ((Ideal.Quotient.mkₐ Λ (T.maximalIdeal ^ n)).comp (tensorLift f g)) a = 0 := sorry

/-- The uncompleted coproduct map on finite adic quotients. -/
def tensorLiftQuot {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T) (n : ℕ) :
    (R.carrier ⊗[Λ] S.carrier) ⧸ tensorAdicIdeal R S ^ n →ₐ[Λ]
      T.carrier ⧸ T.maximalIdeal ^ n :=
  Ideal.Quotient.liftₐ (tensorAdicIdeal R S ^ n)
    ((Ideal.Quotient.mkₐ Λ (T.maximalIdeal ^ n)).comp (tensorLift f g))
    (tensorLift_pow_eq_zero f g n)

/-- `tensorLiftQuot` evaluates on residue classes by the uncompleted coproduct map. -/
theorem tensorLiftQuot_mk {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T)
    (n : ℕ) (a : R.carrier ⊗[Λ] S.carrier) :
    tensorLiftQuot f g n (Ideal.Quotient.mk (tensorAdicIdeal R S ^ n) a) =
      Ideal.Quotient.mk (T.maximalIdeal ^ n) (tensorLift f g a) := sorry

/-- Compatible family of maps from the completed tensor to finite quotients of the target. -/
def descHomFamily {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T) (n : ℕ) :
    AdicCompletion (tensorAdicIdeal R S) (R.carrier ⊗[Λ] S.carrier) →ₐ[Λ]
      T.carrier ⧸ T.maximalIdeal ^ n :=
  (tensorLiftQuot f g n).comp
    ((AdicCompletion.evalₐ (tensorAdicIdeal R S) n).restrictScalars Λ)

/-- The family `descHomFamily` is compatible with the inverse system of quotients. -/
theorem descHom_compat {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T) :
    ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (descHomFamily f g n) =
        descHomFamily f g m := sorry

/-- Underlying algebra map of the coproduct mediating morphism. -/
def descHom {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T) :
    (tensorAdicCompletion R S).carrier →ₐ[Λ] T.carrier :=
  IsAdicComplete.liftAlgHom T.maximalIdeal (descHomFamily f g) (descHom_compat f g)

/-- The mediating algebra map from the completed tensor is local. -/
theorem descHom_isLocalHom {R S T : CompleteLocalAlgCat Λ k} (f : Hom R T) (g : Hom S T) :
    IsLocalHom (descHom f g) := sorry

/-- The mediating algebra map preserves the chosen residue-field identifications. -/
theorem descHom_residue_compat {R S T : CompleteLocalAlgCat Λ k}
    (f : Hom R T) (g : Hom S T) :
    residueCompat (descHom f g) (descHom_isLocalHom f g) =
      residueIsoHom (tensorAdicCompletion R S) := sorry

/-- Mediating morphism of the binary coproduct in `CompleteLocalAlgCat`. -/
def desc {R S T : CompleteLocalAlgCat Λ k} (f : R ⟶ T) (g : S ⟶ T) :
    tensorAdicCompletion R S ⟶ T :=
  Hom.of (descHom f g) (descHom_isLocalHom f g) (descHom_residue_compat f g)

/-- The underlying algebra map of `desc` is `descHom`. -/
theorem desc_hom {R S T : CompleteLocalAlgCat Λ k} (f : R ⟶ T) (g : S ⟶ T) :
    (desc f g).hom = descHom f g := sorry

/-- The explicit pair cocone on the completed tensor. -/
def binaryCofan (R S : CompleteLocalAlgCat Λ k) : BinaryCofan R S :=
  BinaryCofan.mk (tensorAdicCompletionInl R S) (tensorAdicCompletionInr R S)

/-- The left inclusion followed by `desc` recovers the first factor map. -/
theorem desc_comp_inl {R S T : CompleteLocalAlgCat Λ k} (f : R ⟶ T) (g : S ⟶ T) :
    tensorAdicCompletionInl R S ≫ desc f g = f := sorry

/-- The right inclusion followed by `desc` recovers the second factor map. -/
theorem desc_comp_inr {R S T : CompleteLocalAlgCat Λ k} (f : R ⟶ T) (g : S ⟶ T) :
    tensorAdicCompletionInr R S ≫ desc f g = g := sorry

/-- A morphism out of the completed tensor is uniquely determined by the two factor maps. -/
theorem desc_uniq {R S T : CompleteLocalAlgCat Λ k} (f : R ⟶ T) (g : S ⟶ T)
    (m : tensorAdicCompletion R S ⟶ T)
    (hf : tensorAdicCompletionInl R S ≫ m = f)
    (hg : tensorAdicCompletionInr R S ≫ m = g) :
    m = desc f g := sorry

/-- The completed-tensor cofan is a colimit cofan. -/
def binaryCofanIsColimit (R S : CompleteLocalAlgCat Λ k) :
    IsColimit (binaryCofan R S) :=
  BinaryCofan.IsColimit.mk (binaryCofan R S) (fun f g ↦ desc f g)
    (fun f g ↦ desc_comp_inl f g) (fun f g ↦ desc_comp_inr f g)
    (fun f g m hf hg ↦ desc_uniq f g m hf hg)

/-- Every pair in `CompleteLocalAlgCat Λ k` admits a colimit. -/
instance hasColimit_pair (R S : CompleteLocalAlgCat Λ k) :
    HasColimit (pair R S) :=
  HasColimit.mk ⟨binaryCofan R S, binaryCofanIsColimit R S⟩

/-- Residue-identified Noetherian complete local algebras admit binary coproducts. -/
instance hasBinaryCoproducts : HasBinaryCoproducts (CompleteLocalAlgCat Λ k) :=
  CategoryTheory.Limits.hasBinaryCoproducts_of_hasColimit_pair (CompleteLocalAlgCat Λ k)

end

end CompleteLocalAlgCat
