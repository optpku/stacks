module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap110.Lemma_110_75_1
import StacksCheckRecall

/-!
# Regular functions of affine formal algebraic spaces need not have enough sections
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Remark 87.35.2 (1): there exist affine formal algebraic spaces which are not
McQuillan. -/
@[stacks 0DEK] #check exists_isAffineFormalAlgebraicSpace_not_isMcQuillan

/-- Inverse-limit global sections of a directed affine thickening presentation:
compatible families of sections of `Γ(X_i, ⊤)` along `appTop`. -/
def limitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) :
    Type (max u v) :=
  { s : (i : Λ) → (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u) //
    ∀ {i j : Λ} (f : i ⟶ j),
      ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s j) = s i }

/-- Pointwise commutative ring structure on inverse-limit global sections,
inherited from the stage rings `Γ(X_i, ⊤)`. -/
instance instCommRingLimitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) : CommRing (limitGlobalSections D) where
  zero := ⟨fun _ ↦ 0, sorry⟩
  one := ⟨fun _ ↦ 1, sorry⟩
  add x y := ⟨fun i ↦ x.val i + y.val i, sorry⟩
  neg x := ⟨fun i ↦ -x.val i, sorry⟩
  sub x y := ⟨fun i ↦ x.val i - y.val i, sorry⟩
  mul x y := ⟨fun i ↦ x.val i * y.val i, sorry⟩
  nsmul n x := ⟨fun i ↦ n • x.val i, sorry⟩
  zsmul n x := ⟨fun i ↦ n • x.val i, sorry⟩
  npow n x := ⟨fun i ↦ x.val i ^ n, sorry⟩
  natCast n := ⟨fun _ ↦ n, sorry⟩
  intCast n := ⟨fun _ ↦ n, sorry⟩
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg_add_cancel := sorry
  add_comm := sorry
  sub_eq_add_neg := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  npow_zero := sorry
  npow_succ := sorry
  left_distrib := sorry
  right_distrib := sorry
  mul_comm := sorry
  zero_mul := sorry
  mul_zero := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  intCast_ofNat := sorry
  intCast_negSucc := sorry

/-- A family of stage global sections is a point of `limitGlobalSections D`
if and only if it is compatible under `appTop` along morphisms of `D`. -/
theorem mem_limitGlobalSections_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (s : (i : Λ) → (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)) :
    (∃ p : limitGlobalSections D, p.val = s) ↔
      ∀ {i j : Λ} (f : i ⟶ j),
        ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s j) = s i := sorry

/-- Inverse-limit families of global sections are compatible under `appTop`. -/
theorem limitGlobalSections_compatible {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    {D : Λ ⥤ 𝒮.bigAffineSite S} (s : limitGlobalSections D)
    {i j : Λ} (f : i ⟶ j) :
    ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s.val j) = s.val i :=
  sorry

/-- Remark 87.35.2 (2): there exists an affine formal algebraic space whose
regular functions do not separate points: some directed affine thickening
presentation has inverse-limit global sections a field, while some stage
(hence the reduced space) is infinite. -/
@[stacks 0DEK]
theorem exists_isAffineFormalAlgebraicSpace_regularFunctions_not_separatePoints :
    ∃ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v))))
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v))),
      IsAffineFormalAlgebraicSpace X ∧
        ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ 𝒮.bigAffineSite S),
          IsDirectedAffineThickeningColimit D X ∧
            IsField (limitGlobalSections D) ∧
              ∃ i : Λ, Infinite ((𝒮.bigAffineToScheme S).obj (D.obj i)) :=
  sorry

end AlgebraicGeometry
