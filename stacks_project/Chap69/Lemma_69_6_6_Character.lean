module

public import Mathlib.GroupTheory.Perm.Sign
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import stacks_project.Chap66.Lemma_66_18_12_Comparison
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap69.Definition_69_6_2_Koszul
public import stacks_project.Chap69.Lemma_69_6_4_OffDiagonal
public import stacks_project.Chap69.Lemma_69_6_5_Quotient

/-!
# Sign character and twisted restriction on off-diagonal quotients

The sign character `χ_p` of `S_{p+1}` is the universe-lifted permutation sign.
Twisting the restriction of an abelian étale sheaf along a free quotient of the
off-diagonal locus recovers the coefficient sheaf `F|_{U_p} ⊗_ℤ ℤ̲(χ_p)`.
The twist is assembled from `sheafPushforwardAbelian`, `constantIntegerSheaf`,
and `tensorObj`, because `Lemma_69_6_5_Twist` and `Lemma_69_6_4_OffDiagonal`
both export `etaleRestrictionCompIso` and cannot be imported together.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The additive subgroup of `χ`-semi-invariants in an abelian group with a `G`-action. -/
def offDiagonalCharacterInvariantsAddSubgroup {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) : AddSubgroup A where
  carrier := { a | ∀ g : G, (σ g).hom a = ((χ g : ℤˣ) : ℤ) • a }
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- The `χ`-semi-invariants of an abelian group equipped with a `G`-action. -/
noncomputable def offDiagonalCharacterInvariants {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (offDiagonalCharacterInvariantsAddSubgroup σ χ)

/-- The inclusion of `χ`-semi-invariants into the ambient abelian group. -/
noncomputable def offDiagonalCharacterInvariants_ι {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    offDiagonalCharacterInvariants σ χ ⟶ A :=
  AddCommGrpCat.ofHom (offDiagonalCharacterInvariantsAddSubgroup σ χ).subtype

/-- A G-equivariant morphism of ambient abelian groups induces a morphism of
`χ`-semi-invariants. -/
noncomputable def offDiagonalCharacterInvariants_map {G : Type u} [Group G] [Finite G]
    {A B : AddCommGrpCat.{u + 1}} {σA : G →* Aut A} {σB : G →* Aut B}
    (χ : G →* ℤˣ) (ψ : A ⟶ B)
    (h_equivariant : ∀ g : G, (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    offDiagonalCharacterInvariants σA χ ⟶ offDiagonalCharacterInvariants σB χ :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨ψ (a : A), sorry⟩
      map_zero' := sorry
      map_add' := sorry }

variable {W U : AlgebraicSpace S} {G : Type u} [Group G]

/-- Direct image `q_* ℤ̲` on `U_étale`. -/
noncomputable def offDiagonalPushforwardConstantInteger (q : W ⟶ U) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (sheafPushforwardAbelian q).obj (constantIntegerSheaf W)

/-- The identity square of a free quotient morphism is a pullback. -/
theorem offDiagonalIsPullback_smul_comp (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q] (g : G) : IsPullback (ρ g).hom q q (𝟙 U) :=
  sorry

/-- Restriction along an identity morphism is isomorphic to the identity functor
on abelian étale sheaves. -/
noncomputable def offDiagonalEtaleRestrictionSheaf_idIso (X : AlgebraicSpace S) :
    etaleRestrictionSheaf (𝟙 X) AddCommGrpCat.{u + 1} ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (eqToIso (etaleRestriction_id X))
    AddCommGrpCat.{u + 1} (smallEtaleTopology X)

/-- The sheaf morphism `q_* ℤ̲ ⟶ q_* ℤ̲` by base change along `(ρ g).hom`. -/
noncomputable def offDiagonalPushforwardConstantIntegerSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (g : G) :
    offDiagonalPushforwardConstantInteger q ⟶
      offDiagonalPushforwardConstantInteger q :=
  (offDiagonalEtaleRestrictionSheaf_idIso U).inv.app
      (offDiagonalPushforwardConstantInteger q) ≫
    pushforwardEtaleBaseChangeHom (offDiagonalIsPullback_smul_comp ρ q g)
      AddCommGrpCat.{u + 1} (constantIntegerSheaf W) ≫
    (sheafPushforwardAbelian q).map (inv (constantIntegerPullbackHom (ρ g).hom))

/-- The `G`-action on sections of `q_* ℤ̲` over an étale object of `U`. -/
noncomputable def offDiagonalPushforwardConstantIntegerAction
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (V : smallEtaleSite U) :
    G →* Aut ((offDiagonalPushforwardConstantInteger q).obj.obj (op V)) where
  toFun g :=
    { hom := (offDiagonalPushforwardConstantIntegerSmul ρ q g⁻¹).hom.app (op V)
      inv := (offDiagonalPushforwardConstantIntegerSmul ρ q g).hom.app (op V)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- Restriction of sections of `q_* ℤ̲` is G-equivariant. -/
theorem offDiagonalPushforwardConstantInteger_map_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    {V V' : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ V') (g : G) :
    ((offDiagonalPushforwardConstantIntegerAction ρ q (unop V)) g).hom ≫
        (offDiagonalPushforwardConstantInteger q).obj.map f =
      (offDiagonalPushforwardConstantInteger q).obj.map f ≫
        ((offDiagonalPushforwardConstantIntegerAction ρ q (unop V')) g).hom :=
  sorry

variable [Finite G]

/-- The abelian sheaf `ℤ̲(χ) = (q_* ℤ̲)^χ` on `U_étale`. -/
noncomputable def offDiagonalIntegerCharacterAbelianSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} where
  obj :=
    { obj V :=
        offDiagonalCharacterInvariants
          (offDiagonalPushforwardConstantIntegerAction ρ q (unop V)) χ
      map f :=
        offDiagonalCharacterInvariants_map χ
          ((offDiagonalPushforwardConstantInteger q).obj.map f)
          (fun g ↦ offDiagonalPushforwardConstantInteger_map_equivariant ρ q f g)
      map_id := sorry
      map_comp := sorry }
  property := sorry

/-- The sheaf of `ℤ̲_U`-modules `ℤ̲(χ)` on `U_étale`. -/
noncomputable def offDiagonalIntegerCharacterSheaf
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ) :
    SheafOfModules.{u + 1} (integerRingSheaf U) :=
  abelianSheaf_integerModules (offDiagonalIntegerCharacterAbelianSheaf ρ q χ)

/-- Sheaves of modules over the constant integer ring sheaf are monoidal. -/
noncomputable instance instMonoidalCategory_integerRingSheaf (X : AlgebraicSpace S) :
    MonoidalCategory (SheafOfModules.{u + 1} (integerRingSheaf X)) :=
  moduleMonoidalCategory (constantIntegerRingSheaf X)

/-- The abelian sheaf `F ⊗_ℤ ℤ̲(χ)` on `U_étale`. -/
noncomputable def offDiagonalTensorIntegerCharacter
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q] (χ : G →* ℤˣ)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (integerRingSheaf U)).obj
    (tensorObj (abelianSheaf_integerModules F) (offDiagonalIntegerCharacterSheaf ρ q χ))

/-- The sign character of `S_n`, as a homomorphism out of the universe-lifted
symmetric group that acts on the off-diagonal locus. -/
def offDiagonalSignCharacter (n : ℕ) :
    ULift.{u} (Equiv.Perm (Fin n)) →* ℤˣ :=
  Equiv.Perm.sign.comp (MulEquiv.ulift (α := Equiv.Perm (Fin n))).toMonoidHom

/-- `offDiagonalSignCharacter n` evaluates as `Equiv.Perm.sign` on the underlying
permutation. -/
theorem offDiagonalSignCharacter_apply (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    offDiagonalSignCharacter n σ = Equiv.Perm.sign σ.down :=
  rfl

/-- The sheaf `F|_{U_p} ⊗_ℤ ℤ̲(χ_p)` on `U_p,étale`, for a free quotient
`q : W_p ⟶ U_p` of the off-diagonal permutation action and the structure morphism
`π : U_p ⟶ X`. -/
noncomputable def offDiagonalCharacterTwist {U X Up : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (p : ℕ) (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFree (offDiagonalPermLift f (p + 1))]
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q]
    (π : Up ⟶ X) [Etale π] :
    Sheaf (smallEtaleTopology Up) AddCommGrpCat.{u + 1} :=
  offDiagonalTensorIntegerCharacter (offDiagonalPermLift f (p + 1)) q
    (offDiagonalSignCharacter (p + 1))
    ((etaleRestrictionSheaf π AddCommGrpCat.{u + 1}).obj F)

/-- `offDiagonalCharacterTwist` is the integer character twist of the restriction of
`F` along `π`. -/
theorem offDiagonalCharacterTwist_def {U X Up : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (p : ℕ) (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFree (offDiagonalPermLift f (p + 1))]
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q]
    (π : Up ⟶ X) [Etale π] :
    offDiagonalCharacterTwist f F p q π =
      offDiagonalTensorIntegerCharacter (offDiagonalPermLift f (p + 1)) q
        (offDiagonalSignCharacter (p + 1))
        ((etaleRestrictionSheaf π AddCommGrpCat.{u + 1}).obj F) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
