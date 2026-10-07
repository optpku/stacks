module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf.LocallyRinged
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Kummer


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.RelativePicard
open SheafOfModules.RingedSite

noncomputable section
namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
variable (n : ℕ)
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The identity étale morphism, used as the terminal object for degree-zero comparison. -/
noncomputable def etaleCohomologyTerminal : X.left.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 X.left) inferInstance

/-- The identity étale morphism is terminal in the small étale site. -/
noncomputable def etaleCohomologyTerminalIsTerminal :
    IsTerminal (etaleCohomologyTerminal X) :=
  MorphismProperty.Over.mkIdTerminal @Etale X.left

/-- The base-field element obtained by evaluating a degree-zero Kummer class and
inverting the global-sections map. -/
noncomputable def rootsH0BaseValue
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) : k :=
  let rootSection := Sheaf.H.equiv₀
    (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n)
    (etaleCohomologyTerminalIsTerminal X) x
  let unitSection := CategoryTheory.Sheaf.unitsAddSheafUnit
    (smallCommStructureSheaf .etale X.left)
    ((kernel.ι (CategoryTheory.Sheaf.unitsNsmul
      (smallCommStructureSheaf .etale X.left) n)).hom.app
        (op (etaleCohomologyTerminal X)) rootSection)
  let globalUnit := Units.map
    (ULift.ringEquiv : ULift.{u + 1, u} Γ(X.left, ⊤) ≃+* Γ(X.left, ⊤)).toMonoidHom
    unitSection
  Function.invFun (Scheme.Hom.globalSectionsMap X.hom) globalUnit.1

/-- The evaluated Kummer class descends to a unit of the base field. -/
theorem rootsH0BaseValue_isUnit
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    IsUnit (rootsH0BaseValue X n x) := sorry

/-- The descended unit satisfies the defining `n`th-root equation. -/
theorem rootsH0BaseUnit_pow
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    (rootsH0BaseValue_isUnit X n x).unit ^ n = 1 := sorry

/-- The canonical forward function from degree-zero Kummer cohomology to base-field roots of
unity. -/
noncomputable def rootsH0ComparisonFunction
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    Additive (rootsOfUnity n k) :=
  Additive.ofMul
    ⟨(rootsH0BaseValue_isUnit X n x).unit, rootsH0BaseUnit_pow X n x⟩

/-- The degree-zero Kummer comparison preserves addition. -/
theorem rootsH0ComparisonFunction_add
    (x y : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    rootsH0ComparisonFunction X n (x + y) =
      rootsH0ComparisonFunction X n x + rootsH0ComparisonFunction X n y := sorry

/-- The inverse-function presentation is a left inverse to the degree-zero comparison. -/
theorem rootsH0ComparisonFunction_leftInverse
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    Function.invFun (rootsH0ComparisonFunction X n)
        (rootsH0ComparisonFunction X n x) = x := sorry

/-- The inverse-function presentation is a right inverse to the degree-zero comparison. -/
theorem rootsH0ComparisonFunction_rightInverse
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : Additive (rootsOfUnity n k)) :
    rootsH0ComparisonFunction X n
        (Function.invFun (rootsH0ComparisonFunction X n) x) = x := sorry

/-- for a smooth projective curve over an algebraically closed
field and an invertible positive integer `n`, `H^0(X, μₙ)` is identified with
the additive presentation of `rootsOfUnity n k`. -/
noncomputable def etaleCohomology_rootsOfUnity_h0
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    ((Sheaf.functorH X.left.smallEtaleTopology 0).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      Additive (rootsOfUnity n k) where
  toFun := rootsH0ComparisonFunction X n
  invFun := Function.invFun (rootsH0ComparisonFunction X n)
  left_inv := rootsH0ComparisonFunction_leftInverse X n h_pos h_n
  right_inv := rootsH0ComparisonFunction_rightInverse X n h_pos h_n
  map_add' := rootsH0ComparisonFunction_add X n

/-- The forward map of the canonical degree-zero comparison is evaluation at the small étale
terminal object followed by descent along the global-sections map. -/
theorem etaleCohomology_rootsOfUnity_h0_apply
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    etaleCohomology_rootsOfUnity_h0 X n h_pos h_n x =
      rootsH0ComparisonFunction X n x := sorry

/-- An invertible scheme module remains invertible after passage to the small étale site. -/
theorem smallEtaleAssociatedModule_isInvertible
    (L : X.left.Modules) [MonoidalCategory.isInvertibleObject L] :
    MonoidalCategory.isInvertibleObject (smallComm .etale X.left L) := sorry


/-- The canonical function from scheme Picard classes to Picard classes on the small étale
ringed site. -/
noncomputable def schemePicardToSmallEtalePicardFunction
    (x : X.left.PicardGroup) :
    SheafOfModules.RingedSite.PicardGroup X.left.smallEtaleTopology
      (smallCommStructureSheaf .etale X.left) :=
  @MonoidalCategory.PicardGroup.mk
    (SheafOfModules.RingedSite.ringedSiteModuleCategory
      X.left.smallEtaleTopology (smallCommStructureSheaf .etale X.left)) _ _
    (smallComm .etale X.left (Scheme.PicardGroup.repr x))
    (smallEtaleAssociatedModule_isInvertible X (Scheme.PicardGroup.repr x))

/-- The small-étale Picard comparison sends the neutral class to the neutral class. -/
theorem schemePicardToSmallEtalePicardFunction_zero :
    schemePicardToSmallEtalePicardFunction X 0 = 0 := sorry

/-- The small-étale Picard comparison respects addition. -/
theorem schemePicardToSmallEtalePicardFunction_add
    (x y : X.left.PicardGroup) :
    schemePicardToSmallEtalePicardFunction X (x + y) =
      schemePicardToSmallEtalePicardFunction X x +
        schemePicardToSmallEtalePicardFunction X y := sorry

/-- The Picard class underlying a first Kummer cohomology class. -/
noncomputable def rootsH1PicardClassFunction
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) : X.left.PicardGroup :=
  Function.invFun (schemePicardToSmallEtalePicardFunction X)
    (Function.invFun
      (PicardGroup.cohomologyClass
        (smallCommStructureSheaf .etale X.left))
      (Sheaf.H.map
        (kernel.ι (CategoryTheory.Sheaf.unitsNsmul
          (smallCommStructureSheaf .etale X.left) n)) 1 x))

/-- The Picard class underlying a first Kummer class has degree zero. -/
theorem rootsH1PicardClassFunction_mem_degreeZero
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) :
    rootsH1PicardClassFunction X n x ∈ degreeZeroClasses X := sorry

/-- The degree-zero Picard class underlying a first Kummer class is killed by `n`. -/
theorem rootsH1PicardClassFunction_mem_torsion
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) :
    (⟨rootsH1PicardClassFunction X n x,
        rootsH1PicardClassFunction_mem_degreeZero X n h_pos h_n x⟩ :
      degreeZeroClasses X) ∈
        AddSubgroup.torsionBy (degreeZeroClasses X) (n : ℤ) := sorry

/-- The canonical forward function from first Kummer cohomology to degree-zero Picard
`n`-torsion. -/
noncomputable def rootsH1ComparisonFunction
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) :
    AddSubgroup.torsionBy (degreeZeroClasses X) (n : ℤ) :=
  ⟨⟨rootsH1PicardClassFunction X n x,
      rootsH1PicardClassFunction_mem_degreeZero X n h_pos h_n x⟩,
    rootsH1PicardClassFunction_mem_torsion X n h_pos h_n x⟩

/-- The first Kummer comparison preserves addition. -/
theorem rootsH1ComparisonFunction_add
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) :
    rootsH1ComparisonFunction X n h_pos h_n (x + y) =
      rootsH1ComparisonFunction X n h_pos h_n x +
        rootsH1ComparisonFunction X n h_pos h_n y := sorry

/-- The inverse-function presentation is a left inverse to the first Kummer comparison. -/
theorem rootsH1ComparisonFunction_leftInverse
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) :
    Function.invFun (rootsH1ComparisonFunction X n h_pos h_n)
        (rootsH1ComparisonFunction X n h_pos h_n x) = x := sorry

/-- The inverse-function presentation is a right inverse to the first Kummer comparison. -/
theorem rootsH1ComparisonFunction_rightInverse
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : AddSubgroup.torsionBy (degreeZeroClasses X) (n : ℤ)) :
    rootsH1ComparisonFunction X n h_pos h_n
        (Function.invFun (rootsH1ComparisonFunction X n h_pos h_n) x) = x := sorry

/-- in degree one, étale cohomology with coefficients in
`μₙ` is identified with the `n`-torsion of the degree-zero Picard subgroup. -/
noncomputable def etaleCohomology_rootsOfUnity_h1
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    ((Sheaf.functorH X.left.smallEtaleTopology 1).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      AddSubgroup.torsionBy (degreeZeroClasses X) (n : ℤ) where
  toFun := rootsH1ComparisonFunction X n h_pos h_n
  invFun := Function.invFun (rootsH1ComparisonFunction X n h_pos h_n)
  left_inv := rootsH1ComparisonFunction_leftInverse X n h_pos h_n
  right_inv := rootsH1ComparisonFunction_rightInverse X n h_pos h_n
  map_add' := rootsH1ComparisonFunction_add X n h_pos h_n

/-- The forward map of the canonical degree-one comparison is the Kummer-to-Picard map. -/
theorem etaleCohomology_rootsOfUnity_h1_apply
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 1) :
    etaleCohomology_rootsOfUnity_h1 X n h_pos h_n x =
      rootsH1ComparisonFunction X n h_pos h_n x := sorry


/-- Invertibility of `n` over the base field gives invertibility of its image in global
sections. -/
theorem natCast_isUnit_globalSections (h_n : IsUnit (n : k)) :
    IsUnit (n : Γ(X.left, ⊤)) := sorry

/-- The Kummer connecting function from scheme Picard classes to second Kummer cohomology. -/
noncomputable def kummerPicardBoundaryFunction
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : X.left.PicardGroup) :
    (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 2 :=
  let hKummer := kummerSequence_smallEtale_shortExact X.left n h_pos
    (natCast_isUnit_globalSections X n h_n)
  hKummer.extClass.postcomp
    ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (rfl : 1 + 1 = 2)
    (PicardGroup.cohomologyClass
      (smallCommStructureSheaf .etale X.left)
      (schemePicardToSmallEtalePicardFunction X x))

/-- The Kummer boundary sends the neutral Picard class to zero. -/
theorem kummerPicardBoundaryFunction_zero
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    kummerPicardBoundaryFunction X n h_pos h_n 0 = 0 := sorry

/-- The Kummer boundary respects addition of Picard classes. -/
theorem kummerPicardBoundaryFunction_add
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : X.left.PicardGroup) :
    kummerPicardBoundaryFunction X n h_pos h_n (x + y) =
      kummerPicardBoundaryFunction X n h_pos h_n x +
        kummerPicardBoundaryFunction X n h_pos h_n y := sorry

/-- The degree of a Picard class on the curve. -/
noncomputable def curvePicardDegreeFunction (x : X.left.PicardGroup) : ℤ :=
  Scheme.Modules.curveDegreeOfInvertible X.hom
    (topologicalKrullDim_eq_one X).le (Scheme.PicardGroup.repr x)

/-- The degree of the neutral Picard class is zero. -/
theorem curvePicardDegreeFunction_zero : curvePicardDegreeFunction X 0 = 0 := sorry

/-- Picard degree is additive. -/
theorem curvePicardDegreeFunction_add (x y : X.left.PicardGroup) :
    curvePicardDegreeFunction X (x + y) =
      curvePicardDegreeFunction X x + curvePicardDegreeFunction X y := sorry

/-- The canonical forward function from second Kummer cohomology to `ZMod n`, obtained by
taking the degree modulo `n` of a Picard preimage under the Kummer boundary. -/
noncomputable def rootsH2ComparisonFunction
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 2) : ZMod n :=
  (curvePicardDegreeFunction X
    (Function.invFun (kummerPicardBoundaryFunction X n h_pos h_n) x) : ZMod n)

/-- The second Kummer comparison preserves addition. -/
theorem rootsH2ComparisonFunction_add
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 2) :
    rootsH2ComparisonFunction X n h_pos h_n (x + y) =
      rootsH2ComparisonFunction X n h_pos h_n x +
        rootsH2ComparisonFunction X n h_pos h_n y := sorry

/-- The inverse-function presentation is a left inverse to the second Kummer comparison. -/
theorem rootsH2ComparisonFunction_leftInverse
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 2) :
    Function.invFun (rootsH2ComparisonFunction X n h_pos h_n)
        (rootsH2ComparisonFunction X n h_pos h_n x) = x := sorry

/-- The inverse-function presentation is a right inverse to the second Kummer comparison. -/
theorem rootsH2ComparisonFunction_rightInverse
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) (x : ZMod n) :
    rootsH2ComparisonFunction X n h_pos h_n
        (Function.invFun (rootsH2ComparisonFunction X n h_pos h_n) x) = x := sorry

/-- the second étale cohomology group with coefficients in
`μₙ` is identified with `ZMod n`. -/
noncomputable def etaleCohomology_rootsOfUnity_h2
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    ((Sheaf.functorH X.left.smallEtaleTopology 2).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      ZMod n where
  toFun := rootsH2ComparisonFunction X n h_pos h_n
  invFun := Function.invFun (rootsH2ComparisonFunction X n h_pos h_n)
  left_inv := rootsH2ComparisonFunction_leftInverse X n h_pos h_n
  right_inv := rootsH2ComparisonFunction_rightInverse X n h_pos h_n
  map_add' := rootsH2ComparisonFunction_add X n h_pos h_n

/-- The forward map of the canonical degree-two comparison is degree modulo `n` after the
Kummer boundary comparison. -/
theorem etaleCohomology_rootsOfUnity_h2_apply
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 2) :
    etaleCohomology_rootsOfUnity_h2 X n h_pos h_n x =
      rootsH2ComparisonFunction X n h_pos h_n x := sorry

/-- étale cohomology with coefficients in `μₙ` vanishes in
every degree at least three. -/
theorem etaleCohomology_rootsOfUnity_isZero
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) (q : ℕ) (hq : 3 ≤ q) :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) := sorry

/-- after identifying `μₙ` with the constant coefficient
sheaf, degree-zero étale cohomology is noncanonically identified with `ZMod n`. -/
theorem etaleCohomology_constantZMod_h0
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 0).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) ≃+
        ZMod n) := sorry

/-- degree-one étale cohomology with constant `ZMod n`
coefficients is noncanonically identified with `(ZMod n)^(2g)`. -/
theorem etaleCohomology_constantZMod_h1
    (g : ℕ) (h_genus : AlgebraicGeometry.Curve.genus X = g)
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 1).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) ≃+
        (Fin (2 * g) → ZMod n)) := sorry

/-- second étale cohomology with constant `ZMod n`
coefficients is noncanonically identified with `ZMod n`. -/
theorem etaleCohomology_constantZMod_h2
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 2).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) ≃+
        ZMod n) := sorry

/-- étale cohomology with constant `ZMod n` coefficients
vanishes in every degree at least three. -/
theorem etaleCohomology_constantZMod_isZero
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) (q : ℕ) (hq : 3 ≤ q) :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        ((constantSheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) := sorry

end AlgebraicGeometry
end

end
