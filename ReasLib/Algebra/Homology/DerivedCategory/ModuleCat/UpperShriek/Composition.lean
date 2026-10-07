module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange.InternalHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Shift
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Equivalence
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence
public import ReasLib.CategoryTheory.NatTrans.IsIso
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable {a : A →+* B} {b : B →+* C}

section Composition

variable (p : Presentation a) (q : Presentation b)

-- Local instance justification (noncanonical choice): the explicit presentation `p` uniquely fixes the intermediate polynomial-algebra structure on `B` used throughout this section.
local instance compositionPresentationAlgebra : Algebra (MvPolynomial (Fin p.n) A) B :=
  p.map.toAlgebra

/-- The polynomial base-change tensor product is canonically the polynomial algebra over `B`. -/
noncomputable def compositionBaseChangeEquiv :
    (MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[MvPolynomial (Fin p.n) A] B) ≃ₐ[B]
      MvPolynomial (Fin q.n) B :=
  (Algebra.TensorProduct.commRight (MvPolynomial (Fin p.n) A) B
      (MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A))).symm.trans
    (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial (Fin p.n) A) B)

/-- The polynomial base-change equivalence respects the coefficient map from `B`. -/
theorem compositionBaseChangeEquiv_comp_algebraMap :
    (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom.comp
        (algebraMap B
          (MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[MvPolynomial (Fin p.n) A] B)) =
      (MvPolynomial.C : B →+* MvPolynomial (Fin q.n) B) := sorry

/-- The polynomial base-change equivalence respects extension of the first presentation map. -/
theorem compositionBaseChangeEquiv_comp_includeLeft :
    (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeft :
          MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[MvPolynomial (Fin p.n) A]
            MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
              MvPolynomial (Fin p.n) A] B).toRingHom =
      (MvPolynomial.map p.map :
        MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →+*
          MvPolynomial (Fin q.n) B) := sorry

/-- Derived extension through the polynomial base-change tensor product agrees with direct
extension to the polynomial algebra over `B`. -/
public noncomputable def compositionExtensionIso :=
  derivedExtensionOfScalarsCompIso
    (R := B)
    (A := MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
      MvPolynomial (Fin p.n) A] B)
    (B := MvPolynomial (Fin q.n) B)
    (algebraMap B
      (MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
        MvPolynomial (Fin p.n) A] B))
    (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom
    (MvPolynomial.C : B →+* MvPolynomial (Fin q.n) B)
    (compositionBaseChangeEquiv_comp_algebraMap p q)

/-- The outer polynomial algebra is Tor independent of the intermediate presentation target. -/
theorem compositionTorIndependent :
    Tor.IsIndependent
      (ModuleCat.of (MvPolynomial (Fin p.n) A) B)
      (ModuleCat.of (MvPolynomial (Fin p.n) A)
        (MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A))) := sorry

/-- The canonical identification of a polynomial ring in two finite blocks of variables with
an iterated polynomial ring, with the variables for `q` in the outer block. -/
noncomputable def polynomialCompEquiv :
    MvPolynomial (Fin (p.n + q.n)) A ≃ₐ[A]
      MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) :=
  (MvPolynomial.renameEquiv A finSumFinEquiv.symm).trans
    ((MvPolynomial.renameEquiv A (Equiv.sumComm (Fin p.n) (Fin q.n))).trans
      (MvPolynomial.sumAlgEquiv A (Fin q.n) (Fin p.n)))

/-- The iterated polynomial map sends the base-changed polynomial algebra through `q`. -/
noncomputable def iteratedCompMap :
    MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →+* C :=
  (q.map.comp (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom).comp
    (Algebra.TensorProduct.includeLeft :
      MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[MvPolynomial (Fin p.n) A]
        MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
          MvPolynomial (Fin p.n) A] B).toRingHom

/-- The composite polynomial map sends the flattened two blocks of variables through the
iterated presentation map. -/
noncomputable def compMap :
    MvPolynomial (Fin (p.n + q.n)) A →+* C :=
  (iteratedCompMap p q).comp (polynomialCompEquiv p q).toRingHom

/-- The composite polynomial map restricts on coefficients to `b.comp a`. -/
theorem compMap_comp_C :
    (compMap p q).comp MvPolynomial.C = b.comp a := sorry

/-- The composite polynomial map is surjective. -/
theorem compMap_surjective :
    Function.Surjective (compMap p q) := sorry

/-- The composite of two chosen finite polynomial presentations. -/
noncomputable def comp :
    Presentation (b.comp a) :=
  Presentation.ofSurjection (b.comp a) (p.n + q.n) (compMap p q)
    (compMap_comp_C p q) (compMap_surjective p q)

/-- The composite presentation uses the sum of the two numbers of variables. -/
theorem comp_n :
    (comp p q).n = p.n + q.n := sorry

/-- The map of the composite presentation is the explicit composite polynomial map. -/
theorem comp_map :
    (comp p q).map = compMap p q := sorry

/-- Changing from iterated polynomial coordinates to the flattened composite presentation
commutes with derived extension followed by derived coextension. -/
public noncomputable def compositionCoordinateChangeIso :
    (derivedExtensionOfScalars
          (MvPolynomial.C : A →+* MvPolynomial (Fin p.n) A) ⋙
        derivedExtensionOfScalars
          (MvPolynomial.C : MvPolynomial (Fin p.n) A →+*
            MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A))) ⋙
      derivedCoextensionOfScalars (iteratedCompMap p q) ≅
    derivedExtensionOfScalars
        (MvPolynomial.C : A →+* MvPolynomial (Fin (p.n + q.n)) A) ⋙
      derivedCoextensionOfScalars (compMap p q) :=
  Functor.isoWhiskerRight
      (DerivedExtension.Composition.iso
        (MvPolynomial.C : A →+* MvPolynomial (Fin p.n) A)
        (MvPolynomial.C : MvPolynomial (Fin p.n) A →+*
          MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A)))
      (derivedCoextensionOfScalars (iteratedCompMap p q)) ≪≫
    Functor.isoWhiskerRight
      (derivedExtensionOfScalarsCompIso
        (MvPolynomial.C : A →+* MvPolynomial (Fin (p.n + q.n)) A)
        (polynomialCompEquiv p q).toRingHom
        ((MvPolynomial.C : MvPolynomial (Fin p.n) A →+*
            MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A)).comp
          (MvPolynomial.C : A →+* MvPolynomial (Fin p.n) A))
        (polynomialCompEquiv p q).toAlgHom.comp_algebraMap).symm
      (derivedCoextensionOfScalars (iteratedCompMap p q)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (derivedExtensionOfScalars
        (MvPolynomial.C : A →+* MvPolynomial (Fin (p.n + q.n)) A))
      (Functor.isoWhiskerRight
        (derivedExtensionIsoRestrictionOfRingEquiv (polynomialCompEquiv p q).toRingEquiv)
        (derivedCoextensionOfScalars (iteratedCompMap p q))) ≪≫
    Functor.isoWhiskerLeft
      (derivedExtensionOfScalars
        (MvPolynomial.C : A →+* MvPolynomial (Fin (p.n + q.n)) A))
      (Functor.isoWhiskerRight
          (derivedCoextensionIsoRestrictionOfRingEquiv
          (polynomialCompEquiv p q).toRingEquiv).symm
        (derivedCoextensionOfScalars (iteratedCompMap p q))) ≪≫
    Functor.isoWhiskerLeft
      (derivedExtensionOfScalars
        (MvPolynomial.C : A →+* MvPolynomial (Fin (p.n + q.n)) A))
      (DerivedCoextension.compIso (polynomialCompEquiv p q).toRingHom
        (iteratedCompMap p q))

/-- The first coextension comparison after changing polynomial coordinates. -/
public noncomputable def compositionCoordinateCoextensionIso :=
  DerivedCoextension.compIso
    (A := MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
      MvPolynomial (Fin p.n) A] B)
    (B := MvPolynomial (Fin q.n) B) (C := C)
    (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom q.map

/-- The second coextension comparison identifies the iterated map with the composite
presentation map before flattening coordinates. -/
public noncomputable def compositionIteratedCoextensionIso :=
  DerivedCoextension.compIso
    (A := MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A))
    (B := MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
      MvPolynomial (Fin p.n) A] B)
    (C := C)
    (Algebra.TensorProduct.includeLeft :
      MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[MvPolynomial (Fin p.n) A]
        MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
          MvPolynomial (Fin p.n) A] B).toRingHom
    (q.map.comp (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom)

/-- The component of the coordinate-change comparison for derived coextension. -/
public noncomputable def compositionCoordinateComparisonApp
    (K : DerivedCategory
      (ModuleCat (MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A)))) :
    (derivedCoextensionOfScalars q.map).obj
        ((derivedExtensionOfScalars
          (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom).obj
          ((derivedCoextensionOfScalars
            (Algebra.TensorProduct.includeLeft :
              MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[
                MvPolynomial (Fin p.n) A]
                  MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
                    MvPolynomial (Fin p.n) A] B).toRingHom).obj K)) ⟶
      (derivedCoextensionOfScalars (iteratedCompMap p q)).obj K :=
  (derivedCoextensionOfScalars q.map).map
      ((derivedExtensionIsoRestrictionOfRingEquiv
          (compositionBaseChangeEquiv p q).toRingEquiv).hom.app
        ((derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[
              MvPolynomial (Fin p.n) A]
                MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
                  MvPolynomial (Fin p.n) A] B).toRingHom).obj K) ≫
      (derivedCoextensionIsoRestrictionOfRingEquiv
          (compositionBaseChangeEquiv p q).toRingEquiv).inv.app
        ((derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[
              MvPolynomial (Fin p.n) A]
                MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
                  MvPolynomial (Fin p.n) A] B).toRingHom).obj K)) ≫
    (compositionCoordinateCoextensionIso p q).hom.app
        ((derivedCoextensionOfScalars
          (Algebra.TensorProduct.includeLeft :
            MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) →ₐ[
              MvPolynomial (Fin p.n) A]
                MvPolynomial (Fin q.n) (MvPolynomial (Fin p.n) A) ⊗[
                  MvPolynomial (Fin p.n) A] B).toRingHom).obj K) ≫
      (compositionIteratedCoextensionIso p q).hom.app K

/-- The explicit component of the upper-shriek composition comparison attached to two chosen
polynomial presentations. -/
noncomputable def compComparisonApp (K : DerivedCategory (ModuleCat A)) :
    q.functor.obj (p.functor.obj K) ⟶ (p.comp q).functor.obj K :=
  let P := MvPolynomial (Fin p.n) A
  let Q := MvPolynomial (Fin q.n) P
  let T := Q ⊗[P] B
  let QB := MvPolynomial (Fin q.n) B
  let X := (derivedExtensionOfScalars (MvPolynomial.C : A →+* P)).obj K
  let Y := (derivedCoextensionOfScalars p.map).obj X
  let Z := (derivedExtensionOfScalars (MvPolynomial.C : P →+* Q)).obj X
  let extendFromB := derivedExtensionOfScalars (MvPolynomial.C : B →+* QB)
  let changeCoordinates :=
    derivedExtensionOfScalars (compositionBaseChangeEquiv p q).toRingEquiv.toRingHom
  let coextendToTensor := derivedCoextensionOfScalars
    (Algebra.TensorProduct.includeLeft : Q →ₐ[P] T).toRingHom
  let coextendToC := derivedCoextensionOfScalars q.map
  let coextendIterated :
      DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} Q) ⥤
        DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} C) :=
    derivedCoextensionOfScalars (iteratedCompMap p q)
  let shiftB := shiftFunctor (DerivedCategory (ModuleCat.{u, u} B)) (p.n : ℤ)
  let shiftCP := shiftFunctor (DerivedCategory (ModuleCat C)) (p.n : ℤ)
  let shiftCQ := shiftFunctor (DerivedCategory (ModuleCat C)) (q.n : ℤ)
  let shiftCComp := shiftFunctor (DerivedCategory (ModuleCat C)) (p.n + q.n : ℤ)
  let hTor : Tor.IsIndependent (ModuleCat.of P B) (ModuleCat.of P Q) :=
    compositionTorIndependent p q
  let compareExtension :=
    (compositionExtensionIso p q).inv.app Y
  let compareDuality := trivialDualityBaseChangeMap X hTor
  let compareCoordinates :
      coextendToC.obj (changeCoordinates.obj (coextendToTensor.obj Z)) ⟶
        coextendIterated.obj Z :=
    compositionCoordinateComparisonApp p q Z
  let compareUnshifted :
      coextendToC.obj (extendFromB.obj Y) ⟶ coextendIterated.obj Z :=
    coextendToC.map
        (compareExtension ≫ changeCoordinates.map compareDuality) ≫
      compareCoordinates
  let compareShift :
      coextendToC.obj (extendFromB.obj (shiftB.obj Y)) ⟶
        shiftCP.obj (coextendToC.obj (extendFromB.obj Y)) :=
    coextendToC.map ((extendFromB.commShiftIso (p.n : ℤ)).hom.app Y) ≫
      (coextendToC.commShiftIso (p.n : ℤ)).hom.app (extendFromB.obj Y)
  shiftCQ.map compareShift ≫
    shiftCQ.map (shiftCP.map compareUnshifted) ≫
      (shiftFunctorAdd (DerivedCategory (ModuleCat C)) (p.n : ℤ) (q.n : ℤ)).inv.app
        (coextendIterated.obj Z) ≫
        shiftCComp.map ((compositionCoordinateChangeIso p q).hom.app K)

/-- The functorial upper-shriek composition comparison attached to two chosen presentations. -/
noncomputable def compComparison :
    p.functor ⋙ q.functor ⟶ (p.comp q).functor where
  app := compComparisonApp p q
  naturality _ _ _ := sorry

/-- Evaluation of the functorial composition comparison is its explicit component. -/
theorem compComparison_app (K : DerivedCategory (ModuleCat A)) :
    (compComparison p q).app K = compComparisonApp p q K := sorry

/-- Every bounded-below object has an isomorphism component of the upper-shriek composition
comparison. -/
theorem compComparison_app_isIso_of_boundedBelow
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (a : A →+* B) (b : B →+* C)
    (p : Presentation a) (q : Presentation b) (K : DerivedCategory (ModuleCat A))
    (n : ℤ) (hK : K.IsGE n) :
    IsIso ((compComparison p q).app K) := sorry

/-- For finite-type maps of Noetherian rings, the upper-shriek composition comparison is an
isomorphism on the bounded-below part of the derived category. -/
theorem compComparison_isIso_on_boundedBelow
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (a : A →+* B) (b : B →+* C) (ha : a.FiniteType) (hb : b.FiniteType)
    (p : Presentation a) (q : Presentation b) :
    (t.plus : ObjectProperty (DerivedCategory (ModuleCat A))) ≤
      NatTrans.isomorphismLocus (compComparison p q) := sorry

end Composition

end CategoryTheory.ModuleCat.UpperShriek.Presentation
