module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Functoriality
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction

/-!
# Transport of cotangent complexes along isomorphisms

An isomorphic commuting diagram of base and algebra sheaves identifies their
standard cotangent complexes, after restriction to the target coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex ComplexShape
open scoped Simplicial

set_option backward.privateInPublic true

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.Transport

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A A' B B' : Sheaf J CommRingCat.{u}}
variable (eA : A ≅ A') (eB : B ≅ B') (φ : A ⟶ B) (φ' : A' ⟶ B')

private theorem standardTermIso_laws (n : SimplexCategoryᵒᵖ) :
    standardTermRightHom (B := Under.mk φ) (B' := Under.mk φ') eA.hom eB.hom n ≫
      standardTermRightHom (B := Under.mk φ') (B' := Under.mk φ) eA.inv eB.inv n = 𝟙 _ ∧
    standardTermRightHom (B := Under.mk φ') (B' := Under.mk φ) eA.inv eB.inv n ≫
      standardTermRightHom (B := Under.mk φ) (B' := Under.mk φ') eA.hom eB.hom n = 𝟙 _ := by
  sorry

/-- Standard-resolution terms are isomorphic under simultaneous isomorphisms
of the base and the resolved algebra. -/
def termIso (n : SimplexCategoryᵒᵖ) :
    (standardTerm A (Under.mk φ) n).right ≅
      (standardTerm A' (Under.mk φ') n).right where
  hom := standardTermRightHom eA.hom eB.hom n
  inv := standardTermRightHom eA.inv eB.inv n
  hom_inv_id := (standardTermIso_laws eA eB φ φ' n).1
  inv_hom_id := (standardTermIso_laws eA eB φ φ' n).2

private theorem standardTermIso_naturality (h : eA.hom ≫ φ' = φ ≫ eB.hom)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (standardMap A (Under.mk φ) i).right ≫ (termIso eA eB φ φ' m).hom =
      (termIso eA eB φ φ' n).hom ≫ (standardMap A' (Under.mk φ') i).right := by
  sorry

private theorem inverseSquare (h : eA.hom ≫ φ' = φ ≫ eB.hom) :
    eA.inv ≫ φ = φ' ≫ eB.inv := by
  apply (cancel_mono eB.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, eA.inv_hom_id, Category.id_comp]

private def moduleMap {D D' : Sheaf J CommRingCat.{u}}
    {E E' : Sheaf J CommRingCat.{u}} (α : D ⟶ D') (β : E ⟶ E')
    (ψ : D ⟶ E) (ψ' : D' ⟶ E') (h : α ≫ ψ' = ψ ≫ β)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule D (Under.mk ψ)).obj n ⟶
      (restrictionAlong β).obj ((simplicialModule D' (Under.mk ψ')).obj n) :=
  ((ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation D (Under.mk ψ) n))).homEquiv _ _).symm
    (RelativeDifferentials.map
      (show CommSq α (standardTerm D (Under.mk ψ) n).hom
        (standardTerm D' (Under.mk ψ') n).hom
        (standardTermRightHom (B := Under.mk ψ) (B' := Under.mk ψ') α β n) from
          ⟨standardTermRightHom_square (B := Under.mk ψ) (B' := Under.mk ψ') α β h n⟩) ≫
      (restrictionAlong
        (standardTermRightHom (B := Under.mk ψ) (B' := Under.mk ψ') α β n)).map
        ((ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap (standardAugmentation D' (Under.mk ψ') n))).unit.app _) ≫
      (Restriction.compIso'
        (ringSheafMap (standardTermRightHom (B := Under.mk ψ) (B' := Under.mk ψ') α β n))
        (ringSheafMap (standardAugmentation D' (Under.mk ψ') n))
        (ringSheafMap (standardAugmentation D (Under.mk ψ) n ≫ β))
        (standardTermRightHom_comp_augmentation (B := Under.mk ψ) (B' := Under.mk ψ') α β h n)).hom.app _ ≫
      (Restriction.compIso'
        (ringSheafMap (standardAugmentation D (Under.mk ψ) n))
        (ringSheafMap β)
        (ringSheafMap (standardAugmentation D (Under.mk ψ) n ≫ β)) rfl).inv.app _)

private def simplicialHom (h : eA.hom ≫ φ' = φ ≫ eB.hom)
    (n : SimplexCategoryᵒᵖ) :
    (restrictionAlong eB.inv).obj ((simplicialModule A (Under.mk φ)).obj n) ⟶
      (simplicialModule A' (Under.mk φ')).obj n :=
  (restrictionAlong eB.inv).map (moduleMap eA.hom eB.hom φ φ' h n) ≫
    (Restriction.isoCounit ((sheafCompose J (forget₂ CommRingCat RingCat)).mapIso eB)).hom.app _

private def simplicialInv (h : eA.hom ≫ φ' = φ ≫ eB.hom)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A' (Under.mk φ')).obj n ⟶
      (restrictionAlong eB.inv).obj ((simplicialModule A (Under.mk φ)).obj n) :=
  moduleMap eA.inv eB.inv φ' φ (inverseSquare eA eB φ φ' h) n

private theorem simplicialIso_laws (h : eA.hom ≫ φ' = φ ≫ eB.hom)
    (n : SimplexCategoryᵒᵖ) :
    simplicialHom eA eB φ φ' h n ≫ simplicialInv eA eB φ φ' h n = 𝟙 _ ∧
      simplicialInv eA eB φ φ' h n ≫ simplicialHom eA eB φ φ' h n = 𝟙 _ := by
  sorry

private theorem simplicialIso_naturality (h : eA.hom ≫ φ' = φ ≫ eB.hom)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (restrictionAlong eB.inv).map ((simplicialModule A (Under.mk φ)).map i) ≫
      simplicialHom eA eB φ φ' h m =
    simplicialHom eA eB φ φ' h n ≫ (simplicialModule A' (Under.mk φ')).map i := by
  have hn := standardTermIso_naturality eA eB φ φ' h i
  sorry

/-- The standard simplicial cotangent modules agree after transporting the
algebra coefficients along an isomorphism. -/
def simplicialIso (h : eA.hom ≫ φ' = φ ≫ eB.hom) :
    simplicialModule A (Under.mk φ) ⋙ restrictionAlong eB.inv ≅
      simplicialModule A' (Under.mk φ') :=
  NatIso.ofComponents
    (fun n ↦
      { hom := simplicialHom eA eB φ φ' h n
        inv := simplicialInv eA eB φ φ' h n
        hom_inv_id := (simplicialIso_laws eA eB φ φ' h n).1
        inv_hom_id := (simplicialIso_laws eA eB φ φ' h n).2 })
    (fun i ↦ simplicialIso_naturality eA eB φ φ' h i)

private def negativeIso (h : eA.hom ≫ φ' = φ ≫ eB.hom) (n : ℕ) :
    (((restrictionAlong eB.inv).mapHomologicalComplex (up ℤ)).obj
      (obj A (Under.mk φ))).X (-n) ≅ (obj A' (Under.mk φ')).X (-n) :=
  (restrictionAlong eB.inv).mapIso (objXIso A (Under.mk φ) n) ≪≫
    (simplicialIso eA eB φ φ' h).app (op ⦋n⦌) ≪≫
      (objXIso A' (Under.mk φ') n).symm

private def componentIso (h : eA.hom ≫ φ' = φ ≫ eB.hom) :
    ∀ i : ℤ, (((restrictionAlong eB.inv).mapHomologicalComplex (up ℤ)).obj
      (obj A (Under.mk φ))).X i ≅ (obj A' (Under.mk φ')).X i
  | Int.ofNat (Nat.succ k) =>
      (Functor.map_isZero (restrictionAlong eB.inv)
        (isZero_obj_X_of_pos A (Under.mk φ) (by change (0 : ℤ) < (k : ℤ) + 1; omega))).iso
          (isZero_obj_X_of_pos A' (Under.mk φ') (by change (0 : ℤ) < (k : ℤ) + 1; omega))
  | (0 : ℤ) => negativeIso eA eB φ φ' h 0
  | Int.negSucc k => negativeIso eA eB φ φ' h (k + 1)

private theorem iso_comm (h : eA.hom ≫ φ' = φ ≫ eB.hom)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (((restrictionAlong eB.inv).mapHomologicalComplex (up ℤ)).obj
      (obj A (Under.mk φ))).d i j ≫ (componentIso eA eB φ φ' h j).hom =
    (componentIso eA eB φ φ' h i).hom ≫ (obj A' (Under.mk φ')).d i j := by
  sorry

/-- An isomorphic commuting diagram of base and algebra sheaves induces the
canonical isomorphism of standard cotangent complexes over the target algebra. -/
def iso (h : eA.hom ≫ φ' = φ ≫ eB.hom) :
    ((SheafOfModules.restrictScalars (ringSheafMap eB.inv)).mapHomologicalComplex
      (up ℤ)).obj (obj A (Under.mk φ)) ≅ obj A' (Under.mk φ') :=
  HomologicalComplex.Hom.isoOfComponents (componentIso eA eB φ φ' h)
    (fun i j hij ↦ (iso_comm eA eB φ φ' h i j hij).symm)

/-- In nonpositive degrees, the forward map is the transported simplicial comparison. -/
theorem iso_hom_f (h : eA.hom ≫ φ' = φ ≫ eB.hom) (n : ℕ) :
    (iso eA eB φ φ' h).hom.f (-n) =
      (restrictionAlong eB.inv).map (objXIso A (Under.mk φ) n).hom ≫
        (simplicialIso eA eB φ φ' h).hom.app (op ⦋n⦌) ≫
          (objXIso A' (Under.mk φ') n).inv := by
  cases n <;> rfl

/-- In nonpositive degrees, the inverse map is the reverse simplicial comparison. -/
theorem iso_inv_f (h : eA.hom ≫ φ' = φ ≫ eB.hom) (n : ℕ) :
    (iso eA eB φ φ' h).inv.f (-n) =
      (objXIso A' (Under.mk φ') n).hom ≫
        (simplicialIso eA eB φ φ' h).inv.app (op ⦋n⦌) ≫
          (restrictionAlong eB.inv).map (objXIso A (Under.mk φ) n).inv := by
  cases n with
  | zero =>
      change (negativeIso eA eB φ φ' h 0).inv = _
      simp only [negativeIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
        Category.assoc]
      rfl
  | succ n =>
      change (negativeIso eA eB φ φ' h (n + 1)).inv = _
      simp only [negativeIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
        Category.assoc]
      rfl

end SheafOfModules.RingedSite.CotangentComplex.Transport
