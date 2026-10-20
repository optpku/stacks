module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
public import ReasLib.RingTheory.Polynomial.LaurentQuotient
public import ReasLib.Topology.OpenCover.Refinement
public import ReasLib.Topology.Presheaf.Cech.TermIso
public import ReasLib.Topology.Sheaf.Cohomology.Cech.Connecting

/-!
# Čech cohomology of the affine line with doubled origin

This module computes the ordinary Čech cohomology of the structure sheaf on the canonical
two-chart cover and describes the connecting classes of module extensions.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin AlgebraicGeometry.RingedSpace
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite SheafOfModules
open TopologicalSpace TopCat.Sheaf.Cohomology.Cech
open scoped AlgebraicGeometry LaurentPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

variable (k : Type u) [Field k]

/-- The two canonical affine charts of the affine line with doubled origin. -/
def chartCover : Fin 2 → (scheme k 1).Opens :=
  chart k 1

/-- The two affine charts cover the affine line with doubled origin. -/
theorem chartCover_isOpenCover : IsOpenCover (chartCover k) := by
  sorry

/-- The canonical chart family indexed in the universe required by the Čech construction. -/
def chartCoverULift : ULift.{u} (Fin 2) → (scheme k 1).Opens :=
  fun i ↦ chartCover k i.down

/-- Universe lifting preserves the covering property of the two charts. -/
theorem chartCoverULift_isOpenCover : IsOpenCover (chartCoverULift k) := by
  sorry

/-- The bundled open cover of the affine line with doubled origin. -/
def chartOpenCover : OpenCover.{u} (scheme k 1).carrier :=
  OpenCover.ofFamily (chartCoverULift k) (chartCoverULift_isOpenCover k)

/-- Evaluation of the bundled cover recovers its defining family. -/
theorem chartOpenCover_obj (i : ULift.{u} (Fin 2)) :
    chartOpenCover k i = chartCoverULift k i := by
  rfl

/-- The intersection of the two canonical affine charts. -/
abbrev chartOverlap : (scheme k 1).Opens :=
  chartCover k 0 ⊓ chartCover k 1

/-- Restriction from the first affine chart to the overlap. -/
def leftRestriction :
    Γ(scheme k 1, chartCover k 0) →+* Γ(scheme k 1, chartOverlap k) :=
  ((scheme k 1).presheaf.map
      (homOfLE (inf_le_left : chartOverlap k ≤ chartCover k 0)).op).hom

/-- Restriction from the second affine chart to the overlap. -/
def rightRestriction :
    Γ(scheme k 1, chartCover k 1) →+* Γ(scheme k 1, chartOverlap k) :=
  ((scheme k 1).presheaf.map
      (homOfLE (inf_le_right : chartOverlap k ≤ chartCover k 1)).op).hom

/-- The coordinate ring of affine one-space. -/
def chartCoordinateAlgEquiv : coordinateRing k 1 ≃ₐ[k] Polynomial k :=
  MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))

/-- The unique affine coordinate corresponds to the polynomial variable. -/
theorem chartCoordinateAlgEquiv_coordinate :
    chartCoordinateAlgEquiv k (coordinate k 1 0) = Polynomial.X := by
  sorry

/-- The polynomial coordinate map into sections on the chosen affine chart. -/
def chartCoordinateRingHom (i : Fin 2) :
    Polynomial k →+* Γ(scheme k 1, chartCover k i) :=
  (CommRingCat.Hom.hom
      (PuncturedAffineSpace.coordinateRingToGlobalSections (ULift.{u} (Fin 1)) k ≫
        (chartIso k 1 i).hom.appTop ≫ (chart k 1 i).topIso.hom)).comp
    (chartCoordinateAlgEquiv k).symm.toRingHom

/-- There is a coordinate identification of overlap sections with Laurent polynomials under
which both chart restrictions are the canonical polynomial-to-Laurent map. -/
theorem exists_identityGlueingRingEquiv :
    ∃ e : Γ(scheme k 1, chartOverlap k) ≃+* LaurentPolynomial k,
      (∀ p : Polynomial k,
          e (leftRestriction k (chartCoordinateRingHom k 0 p)) = Polynomial.toLaurent p) ∧
      (∀ p : Polynomial k,
          e (rightRestriction k (chartCoordinateRingHom k 1 p)) = Polynomial.toLaurent p) := by
  sorry

/-- The degree-one ordinary Čech cohomology group of the structure module on the two-chart
cover. -/
abbrev cechH1 : AddCommGrpCat.{u} :=
  moduleCechCohomology (chartCoverULift k)
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf) 1

/-- The carrier of the degree-one Čech cohomology group of the structure module. -/
abbrev cechH1Carrier : Type u :=
  cechH1 k

/-- Multiplication by a constant global section on the structure module. -/
def unitMul (a : k) :
    SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf ⟶
      SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf :=
  topSectionMorphism
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)
    (Scheme.Hom.globalSectionsMap (toBase k 1) a)

/-- Scalar multiplication on Čech cohomology induced by multiplication by global constants. -/
def cechH1Smul (a : k) (x : cechH1Carrier k) : cechH1Carrier k :=
  (moduleCechCohomologyFunctor (chartCoverULift k) 1).map (unitMul k a) x

/-- Multiplication by one acts identically on Čech cohomology. -/
theorem cechH1Smul_one : ∀ x : cechH1Carrier k, cechH1Smul k 1 x = x := by
  intro x
  sorry

/-- Scalar multiplication on Čech cohomology respects multiplication of constants. -/
theorem cechH1Smul_mul : ∀ a b : k, ∀ x : cechH1Carrier k,
    cechH1Smul k (a * b) x = cechH1Smul k a (cechH1Smul k b x) := by
  intro a b x
  sorry

/-- Scalar multiplication sends zero cohomology classes to zero. -/
theorem cechH1Smul_zero : ∀ a : k, cechH1Smul k a 0 = 0 := by
  intro a
  sorry

/-- Scalar multiplication distributes over addition of cohomology classes. -/
theorem cechH1Smul_add : ∀ a : k, ∀ x y : cechH1Carrier k,
    cechH1Smul k a (x + y) = cechH1Smul k a x + cechH1Smul k a y := by
  intro a x y
  sorry

/-- Addition of constants acts by the sum of the corresponding scalar actions. -/
theorem cechH1Smul_add_scalar : ∀ a b : k, ∀ x : cechH1Carrier k,
    cechH1Smul k (a + b) x = cechH1Smul k a x + cechH1Smul k b x := by
  intro a b x
  sorry

/-- Zero acts by zero on Čech cohomology. -/
theorem cechH1Smul_zero_scalar : ∀ x : cechH1Carrier k, cechH1Smul k 0 x = 0 := by
  intro x
  sorry

/-- The natural scalar multiplication makes Čech cohomology a vector space over the field. -/
noncomputable instance cechH1Module : Module k (cechH1Carrier k) where
  smul := cechH1Smul k
  one_smul := cechH1Smul_one k
  mul_smul := cechH1Smul_mul k
  smul_zero := cechH1Smul_zero k
  smul_add := cechH1Smul_add k
  add_smul := cechH1Smul_add_scalar k
  zero_smul := cechH1Smul_zero_scalar k

/-- The inferred module scalar operation is the geometric scalar action. -/
theorem cechH1Module_smul (a : k) (x : cechH1Carrier k) :
    a • x = cechH1Smul k a x := rfl

private def mixed01 : Fin 2 → ULift.{u} (Fin 2) := ULift.up

private def mixed10 : Fin 2 → ULift.{u} (Fin 2) :=
  fun i ↦ ULift.up (1 - i)

private def overlapRestrictMixed01 (α : Γ(scheme k 1, chartOverlap k)) :
    ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
      (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)).obj
      (op (TopCat.Presheaf.Cech.intersection (chartCoverULift k) mixed01)) :=
  ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)).map
    (homOfLE
      (le_inf (iInf_le (fun a ↦ chartCoverULift k (mixed01 a)) 0)
        (iInf_le (fun a ↦ chartCoverULift k (mixed01 a)) 1))).op α

private def overlapRestrictMixed10 (α : Γ(scheme k 1, chartOverlap k)) :
    ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
      (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)).obj
      (op (TopCat.Presheaf.Cech.intersection (chartCoverULift k) mixed10)) :=
  ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)).map
    (homOfLE
      (le_inf (iInf_le (fun a ↦ chartCoverULift k (mixed10 a)) 1)
        (iInf_le (fun a ↦ chartCoverULift k (mixed10 a)) 0))).op α

/-- The overlap section defines a Čech cochain with the prescribed signs on the two mixed
pairs. -/
@[no_expose]
def overlapCocycle (α : Γ(scheme k 1, chartOverlap k)) :
    TopCat.Presheaf.Cech.term (chartCoverULift k)
      ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
        (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)) 1 :=
  fun σ ↦
    if h : σ = mixed01 then
      h ▸ overlapRestrictMixed01 k α
    else if h' : σ = mixed10 then
      h' ▸ (-overlapRestrictMixed10 k α)
    else
      0

/-- The transported overlap cochain is a cycle in the ordinary Čech complex. -/
theorem overlapCocycle_isCocycle (α : Γ(scheme k 1, chartOverlap k)) :
    let K := TopCat.Presheaf.cechComplex (chartCoverULift k)
      ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
        (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf))
    K.d 1 2 ((TopCat.Presheaf.Cech.termIso (chartCoverULift k)
      ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
        (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)) 1).inv
      (overlapCocycle k α)) = 0 := by
  sorry

/-- The Čech class of an overlap section on the two-chart cover. -/
def cechClassOfOverlapSection (α : Γ(scheme k 1, chartOverlap k)) : cechH1 k :=
  (moduleCechComplex (chartCoverULift k)
      (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)).homologyπ 1
    (Function.invFun (fun z ↦
      (moduleCechComplex (chartCoverULift k)
        (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)).iCycles 1 z)
      ((TopCat.Presheaf.Cech.termIso (chartCoverULift k)
        ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
          (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)) 1).inv
        (overlapCocycle k α)))

/-- Every cycle representing the overlap cochain has the class assigned to that cochain. -/
theorem cechClassOfOverlapSection_spec (α : Γ(scheme k 1, chartOverlap k)) :
    let K := moduleCechComplex (chartCoverULift k)
      (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)
    ∀ z : K.cycles 1,
      K.iCycles 1 z = (TopCat.Presheaf.Cech.termIso (chartCoverULift k)
        ((moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
          (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)) 1).inv
        (overlapCocycle k α) →
        cechClassOfOverlapSection k α = K.homologyπ 1 z := by
  sorry

/-- The zero overlap section gives the zero Čech class. -/
theorem cechClassOfOverlapSection_zero :
    cechClassOfOverlapSection k 0 = 0 := by
  sorry

/-- The structure sheaf, considered as a module over itself. -/
abbrev unitModule : (scheme k 1).toRingedSpace.Modules :=
  SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf

/-- Module morphisms with zero composite also have zero composite as additive sheaf maps. -/
theorem underlyingAbelianMap_comp_eq_zero {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) :
    (moduleUnderlyingSheaf (scheme k 1).toRingedSpace).map ι ≫
      (moduleUnderlyingSheaf (scheme k 1).toRingedSpace).map π = 0 := by
  sorry

/-- The underlying additive short complex of a sequence of module morphisms with zero
composite. -/
def underlyingExtensionComplex {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) :
    ShortComplex ((scheme k 1).carrier.Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk
    ((moduleUnderlyingSheaf (scheme k 1).toRingedSpace).map ι)
    ((moduleUnderlyingSheaf (scheme k 1).toRingedSpace).map π)
    (underlyingAbelianMap_comp_eq_zero k ι π w)

/-- The underlying additive short complex is short exact whenever the module sequence is. -/
theorem underlyingExtensionComplex_shortExact {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0)
    (h : (ShortComplex.mk ι π w).ShortExact) :
    (underlyingExtensionComplex k ι π w).ShortExact := by
  sorry

/-- A family of local sections of a module sheaf on the fixed cover. -/
abbrev localSectionFamily (E : (scheme k 1).toRingedSpace.Modules) : Type u :=
  ∀ i : ULift.{u} (Fin 2),
    ((moduleUnderlyingSheaf (scheme k 1).toRingedSpace).obj E).presheaf.obj
      (op (chartCoverULift k i))

/-- The local sections lift the restriction of the global unit section. -/
def IsLiftOfUnit {E : (scheme k 1).toRingedSpace.Modules}
    (π : E ⟶ unitModule k) (s : localSectionFamily k E) : Prop :=
  ∀ i : ULift.{u} (Fin 2),
    ((moduleUnderlyingSheaf (scheme k 1).toRingedSpace).map π).hom.app
        (op (chartCoverULift k i)) (s i) =
      ((moduleUnderlyingSheaf (scheme k 1).toRingedSpace).obj (unitModule k)).presheaf.map
        (homOfLE (le_top : chartCoverULift k i ≤ ⊤)).op
        (unitTopValue (scheme k 1).toRingedSpace)

/-- The coverwise connecting class of local lifts of the unit section for an extension. -/
def extensionCoverwiseClass {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0)
    (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s) : cechH1 k :=
  coverwiseClass
    (@Lift.ofFamily (scheme k 1).carrier (underlyingExtensionComplex k ι π w)
      (unitTopValue (scheme k 1).toRingedSpace) (chartOpenCover k) s hs)

/-- The stage image of the coverwise extension class is the Čech boundary of the global
unit section. -/
theorem extensionCoverwiseClass_delta {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0)
    (h : (ShortComplex.mk ι π w).ShortExact)
    (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s) :
    stageMap.{u, u, u} (chartOpenCover k)
      ((moduleUnderlyingSheaf (scheme k 1).toRingedSpace).obj (unitModule k)) 1
      (ULift.up (extensionCoverwiseClass k ι π w s hs)) =
    delta (underlyingExtensionComplex_shortExact k ι π w h)
      (ULift.up (unitTopValue (scheme k 1).toRingedSpace)) := by
  sorry

/-- A Čech class is the connecting value of the given module extension when local lifts of the
unit section realize it on the two-chart cover. -/
def IsCoverwiseConnectingClass {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) (c : cechH1 k) : Prop :=
  ∃ (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s),
    extensionCoverwiseClass k ι π w s hs = c

/-- The connecting-class predicate is equivalent to the existence of local lifts with the
prescribed class. -/
theorem isCoverwiseConnectingClass_iff {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) (c : cechH1 k) :
    IsCoverwiseConnectingClass k ι π w c ↔
      ∃ (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s),
        extensionCoverwiseClass k ι π w s hs = c := Iff.rfl

/-- Čech cohomology of the two-chart cover is the Laurent quotient, with the negative powers as
a basis and both chart restrictions given by the identity Laurent coordinate. -/
theorem cechH1_basis (k : Type u) [Field k] :
    ∃ (e : Γ(scheme k 1, chartOverlap k) ≃+* LaurentPolynomial k)
      (φ : cechH1Carrier k ≃ₗ[k] LaurentPolynomial.quotientByPolynomials k),
      (∀ p : Polynomial k,
          e (leftRestriction k (chartCoordinateRingHom k 0 p)) = Polynomial.toLaurent p) ∧
      (∀ p : Polynomial k,
          e (rightRestriction k (chartCoordinateRingHom k 1 p)) = Polynomial.toLaurent p) ∧
      (∀ n : {n : ℕ // 0 < n},
          φ (cechClassOfOverlapSection k
            (e.symm (LaurentPolynomial.T (-(n : ℤ))))) =
            LaurentPolynomial.quotientByPolynomialsMk k
              (LaurentPolynomial.T (-(n : ℤ)))) ∧
      Function.Bijective
        (Finsupp.linearCombination k
          (fun n : {n : ℕ // 0 < n} ↦
            cechClassOfOverlapSection k
              (e.symm (LaurentPolynomial.T (-(n : ℤ)))))) := by
  sorry

/-- Every degree-one Čech class is the connecting value of a short exact extension of the
structure module by itself. -/
theorem exists_extension_of_cechClass (k : Type u) [Field k] (c : cechH1 k) :
    ∃ (E : (scheme k 1).toRingedSpace.Modules) (ι : unitModule k ⟶ E)
      (π : E ⟶ unitModule k) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact ∧ IsCoverwiseConnectingClass k ι π w c := by
  sorry

end AlgebraicGeometry.DoubledOrigin

end
