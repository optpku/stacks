module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Cohomology
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Braiding
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology products on derived module categories

@stack 068H

This file owns the chain-level cohomology product for module complexes and its transport to an
explicit derived tensor model. The tensor model and monoidal localization comparison remain
visible inputs: no ambient derived monoidal structure is inferred or reconstructed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

open HomologicalComplex

/-- The tensor of two cycle inclusions has zero differential in total cochain degree i + j. -/
@[stacks 068H "cycle tensors are cycles in total degree"]
lemma cycleTensorToComponent_d_eq_zero
    (K L : CochainComplex (ModuleCat R) ℤ) (i j : ℤ) :
    ((((K.iCycles i) ⊗ₘ (L.iCycles j) : K.cycles i ⊗ L.cycles j ⟶ K.X i ⊗ L.X j) ≫
      (HomologicalComplex.ιTensorObj K L i j (i + j) rfl :
        K.X i ⊗ L.X j ⟶ (K ⊗ L).X (i + j))) ≫
      (K ⊗ L).d (i + j) (i + j + 1) = 0) := sorry

/-- The chain-level product map on cohomology for cochain complexes of R-modules. -/
@[stacks 068H "chain-level cohomology product"]
noncomputable def cochainCohomologyProduct
    (K L : CochainComplex (ModuleCat R) ℤ) (i j : ℤ) :
    K.homology i ⊗ L.homology j ⟶ (K ⊗ L).homology (i + j) :=
  let target : ModuleCat R := (K ⊗ L).homology (i + j)
  let f0 : K.cycles i ⊗ L.cycles j ⟶ target :=
    (K ⊗ L).liftCycles
      (((((K.iCycles i) ⊗ₘ (L.iCycles j) :
          K.cycles i ⊗ L.cycles j ⟶ K.X i ⊗ L.X j) ≫
        (HomologicalComplex.ιTensorObj K L i j (i + j) rfl :
          K.X i ⊗ L.X j ⟶ (K ⊗ L).X (i + j))) :
          K.cycles i ⊗ L.cycles j ⟶ (K ⊗ L).X (i + j)))
      (i + j + 1) (by simp)
      (cycleTensorToComponent_d_eq_zero K L i j) ≫
        (K ⊗ L).homologyπ (i + j)
  let g0 : L.cycles j ⟶ (ihom (K.cycles i)).obj target :=
    MonoidalClosed.curry f0
  let hg0 : (L.sc j).toCycles ≫ g0 = 0 := by
    sorry
  let g1 : L.homology j ⟶ (ihom (K.cycles i)).obj target :=
    (L.sc j).descHomology g0 hg0
  let f1 : K.cycles i ⊗ L.homology j ⟶ target :=
    MonoidalClosed.uncurry g1
  let g1' : K.cycles i ⟶ (ihom (L.homology j)).obj target :=
    MonoidalClosed.curry
      (((β_ (L.homology j) (K.cycles i)).hom :
          L.homology j ⊗ K.cycles i ⟶ K.cycles i ⊗ L.homology j) ≫ f1)
  let hg1' : (K.sc i).toCycles ≫ g1' = 0 := by
    sorry
  let g2 : K.homology i ⟶ (ihom (L.homology j)).obj target :=
    (K.sc i).descHomology g1' hg1'
  ((β_ (K.homology i) (L.homology j)).hom :
      K.homology i ⊗ L.homology j ⟶ L.homology j ⊗ K.homology i) ≫
    MonoidalClosed.uncurry g2

variable [hD : HasDerivedCategory (ModuleCat R)]
variable [MonoidalCategory (DerivedCategory (ModuleCat R))]
variable [(DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
    DerivedCategory (ModuleCat R)).Monoidal]
variable (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))

/-- Compare the tensor of chosen complex preimages with a supplied derived tensor model for a
chosen presentation of the derived category. -/
@[stacks 068H "preimage tensor comparison isomorphism"]
noncomputable def preimageTensorIsoWith (K L : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)).obj
      (DerivedCategory.Q.objPreimage K ⊗ DerivedCategory.Q.objPreimage L) ≅ K ⊗[R]^L L :=
  let KQ : CochainComplex (ModuleCat R) ℤ ⥤
      HomotopyCategory (ModuleCat R) (up ℤ) :=
    HomotopyCategory.quotient (ModuleCat R) (up ℤ)
  let Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
      DerivedCategory (ModuleCat R) := DerivedCategory.Qh
  ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
      (DerivedCategory.Q.objPreimage K ⊗ DerivedCategory.Q.objPreimage L)).symm ≪≫
    Qh.mapIso
      ((Functor.Monoidal.μIso KQ
        (DerivedCategory.Q.objPreimage K)
        (DerivedCategory.Q.objPreimage L)).symm) ≪≫
    (Functor.Monoidal.μIso Qh
      (KQ.obj (DerivedCategory.Q.objPreimage K))
      (KQ.obj (DerivedCategory.Q.objPreimage L))).symm ≪≫
    (((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        (DerivedCategory.Q.objPreimage K)) ⊗ᵢ
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        (DerivedCategory.Q.objPreimage L))) ≪≫
    (DerivedCategory.Q.objObjPreimageIso K ⊗ᵢ DerivedCategory.Q.objObjPreimageIso L) ≪≫
      (T.objIsoTensor K L).symm

/-- The derived cohomology product for a chosen derived-category presentation, transported
through an explicit derived tensor model. -/
@[stacks 068H "derived cohomology product"]
noncomputable def derivedCohomologyProductWith (i j : ℤ)
    (K L : DerivedCategory (ModuleCat R)) :
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K ⊗
      (DerivedCategory.homologyFunctor (ModuleCat R) j).obj L) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).obj (K ⊗[R]^L L) :=
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  ((((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
        (DerivedCategory.Q.objObjPreimageIso K)).inv ⊗ₘ
      ((DerivedCategory.homologyFunctor (ModuleCat R) j).mapIso
        (DerivedCategory.Q.objObjPreimageIso L)).inv) ≫
    (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K') ⊗ₘ
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) j).hom.app L')) ≫
    cochainCohomologyProduct K' L' i j ≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (i + j)).inv.app (K' ⊗ L')) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).map
        (preimageTensorIsoWith T K L).hom)

end

section

variable {R : Type u} [CommRing R]

/-- Compare chosen complex preimages with the standard module derived tensor model. -/
noncomputable def preimageTensorIso
    [MonoidalCategory (DerivedCategory (ModuleCat R))]
    [(DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
      DerivedCategory (ModuleCat R)).Monoidal]
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))
    (K L : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)).obj
        (DerivedCategory.Q.objPreimage K ⊗ DerivedCategory.Q.objPreimage L) ≅ K ⊗[R]^L L :=
  @preimageTensorIsoWith R _ (ModuleCat.hasDerivedCategory R) _ _ T K L

/-- The standard-presentation derived cohomology product transported through an explicit derived
tensor model. -/
noncomputable def derivedCohomologyProduct
    [MonoidalCategory (DerivedCategory (ModuleCat R))]
    [(DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
      DerivedCategory (ModuleCat R)).Monoidal]
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat R))
    (i j : ℤ)
    (K L : DerivedCategory (ModuleCat R)) :
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K ⊗
      (DerivedCategory.homologyFunctor (ModuleCat R) j).obj L) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).obj (K ⊗[R]^L L) :=
  @derivedCohomologyProductWith R _ (ModuleCat.hasDerivedCategory R) _ _ T i j K L

end

end CategoryTheory
