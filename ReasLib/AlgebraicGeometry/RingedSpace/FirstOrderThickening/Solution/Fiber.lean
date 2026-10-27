/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Functoriality

/-!
# The Ext¹ fibre classifying first-order ringed-space solutions

Solution classes are canonically equivalent to the fibre of derived restriction over the
coefficient image of the tautological extension class.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

/-- The tautological identity-base diagram induces the zero kernel map. -/
private theorem selfSolution_induces :
    kernelMapOf (𝟙 S') t t inferInstance (𝟙 S') rfl ≫
      (t _*).map (Iso.refl (Hom.idealModule t)).hom =
        zeroKernelMap t (Hom.idealModule t) := sorry

/-- The tautological solution of the identity diagram, with middle space `S'`. -/
def selfSolution : Solution (𝟙 S') t (Hom.idealModule t) (zeroKernelMap t (Hom.idealModule t)) :=
  Solution.of (𝟙 S') t (Hom.idealModule t) (zeroKernelMap t (Hom.idealModule t))
    t (𝟙 S') rfl (Iso.refl _) (by exact selfSolution_induces t)

/-- The carrier of the tautological solution is `S'`. -/
theorem selfSolution_space : (selfSolution t).space = S' := sorry

/-- The thickening of the tautological solution is `t`. -/
theorem selfSolution_i : (selfSolution t).i = t := sorry

/-- The structure map of the tautological solution is the identity on `S'`. -/
theorem selfSolution_f' : (selfSolution t).f' = 𝟙 S' := sorry

/-- The Ext¹ class of the tautological extension of `𝒪_S` by the kernel of `t`. -/
def selfExtensionClass :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := S.Modules)).obj NL[t],
      (DerivedCategory.Q (C := S.Modules)).obj
        ((CochainComplex.singleFunctor S.Modules 0).obj (Hom.idealModule t))) :=
  (extensionEquiv t (Hom.idealModule t)).symm (isoClassMk (selfSolution t))

/-- The tautological class is the inverse extension-classification image of its solution. -/
theorem selfExtensionClass_spec :
    selfExtensionClass t =
      (extensionEquiv t (Hom.idealModule t)).symm (isoClassMk (selfSolution t)) := sorry

/-- A solution's square also commutes after forgetting to the identity base. -/
private theorem toIdentitySolution_commutes (sol : Solution t f G c) :
    sol.i ≫ sol.f' = (f ≫ t) ≫ 𝟙 S' := sorry

/-- Forgetting to the identity base induces the zero kernel map. -/
private theorem toIdentitySolution_induces (sol : Solution t f G c) :
    kernelMapOf (𝟙 S') (f ≫ t) sol.i sol.i_isFirstOrder sol.f'
        (toIdentitySolution_commutes t f G c sol) ≫
      ((f ≫ t) _*).map sol.kernelIso.hom = zeroKernelMap (f ≫ t) G := sorry

/-- Forget a deformation solution to its relative square-zero algebra extension. -/
def toIdentitySolution (sol : Solution t f G c) :
    Solution (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G) where
  space := sol.space
  i := sol.i
  i_isFirstOrder := sol.i_isFirstOrder
  f' := sol.f'
  commutes := by exact toIdentitySolution_commutes t f G c sol
  kernelIso := sol.kernelIso
  induces_c := by exact toIdentitySolution_induces t f G c sol

/-- Forgetting to the identity diagram preserves the middle ringed space. -/
theorem toIdentitySolution_space (sol : Solution t f G c) :
    (toIdentitySolution t f G c sol).space = sol.space := sorry

/-- Forgetting to the identity diagram preserves the thickening of `X`. -/
theorem toIdentitySolution_i (sol : Solution t f G c) :
    (toIdentitySolution t f G c sol).i = sol.i := sorry

/-- Forgetting to the identity diagram preserves the structure map to `S'`. -/
theorem toIdentitySolution_f' (sol : Solution t f G c) :
    (toIdentitySolution t f G c sol).f' = sol.f' := sorry

/-- Isomorphic solutions have the same class of their underlying algebra extensions. -/
private theorem toExtClass_respectsIso (first second : Solution t f G c)
    (h : (isoSetoid t f G c).r first second) :
    (extensionEquiv (f ≫ t) G).symm (isoClassMk (toIdentitySolution t f G c first)) =
      (extensionEquiv (f ≫ t) G).symm
        (isoClassMk (toIdentitySolution t f G c second)) := sorry

/-- The Ext¹ class of the relative algebra extension underlying a solution class. -/
def toExtClass (p : IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f ≫ t],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  Quotient.liftOn p
    (fun sol ↦
      (extensionEquiv (f ≫ t) G).symm (isoClassMk (toIdentitySolution t f G c sol)))
    (by exact toExtClass_respectsIso t f G c)

/-- The Ext¹ class on a representative is the inverse extension-classification image. -/
theorem toExtClass_mk (sol : Solution t f G c) :
    toExtClass t f G c (isoClassMk sol) =
      (extensionEquiv (f ≫ t) G).symm (isoClassMk (toIdentitySolution t f G c sol)) := sorry

/-- The fibre of derived restriction over the coefficient image of the tautological class. -/
abbrev solutionExtFiber :=
  {ζ :
      Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f ≫ t],
        (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) //
    extOne_comap t f ζ = extOne_map (cPull t f c) (selfExtensionClass t)}

/-- A fibre element restricts to the coefficient image of the tautological class. -/
theorem mem_solutionExtFiber (ζ : solutionExtFiber t f G c) :
    extOne_comap t f ζ.val = extOne_map (cPull t f c) (selfExtensionClass t) := sorry

/-- An identity-base extension commutes with the original base thickening. -/
private theorem ofFiber_commutes
    (SB : Solution (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G)) :
    SB.i ≫ SB.f' = f ≫ t := sorry

/-- An extension with the prescribed restricted class induces the prescribed kernel map. -/
private theorem ofFiber_induces
    (SB : Solution (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G))
    (h : extOne_comap t f ((extensionEquiv (f ≫ t) G).symm (isoClassMk SB)) =
      extOne_map (cPull t f c) (selfExtensionClass t)) :
    kernelMapOf t f SB.i SB.i_isFirstOrder SB.f' (ofFiber_commutes t f G SB) ≫
      (f _*).map SB.kernelIso.hom = c := sorry

/-- Reinterpret an identity-base extension with the prescribed restricted class as a solution. -/
def ofCompatibleIdentitySolution
    (SB : Solution (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G))
    (h : extOne_comap t f ((extensionEquiv (f ≫ t) G).symm (isoClassMk SB)) =
      extOne_map (cPull t f c) (selfExtensionClass t)) : Solution t f G c where
  space := SB.space
  i := SB.i
  i_isFirstOrder := SB.i_isFirstOrder
  f' := SB.f'
  commutes := by exact ofFiber_commutes t f G SB
  kernelIso := SB.kernelIso
  induces_c := by exact ofFiber_induces t f G c SB h

/-- Compatible reconstruction as a function of its certificate respects extension isomorphism. -/
private theorem ofCompatibleIdentitySolution_congr
    (first second : Solution (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G))
    (h : (isoSetoid (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G)).r first second) :
    HEq (fun hCompatibility ↦
      isoClassMk (ofCompatibleIdentitySolution t f G c first hCompatibility))
      (fun hCompatibility ↦
        isoClassMk (ofCompatibleIdentitySolution t f G c second hCompatibility)) := sorry

/-- Classifying a fibre element as an algebra extension preserves its compatibility equality. -/
private theorem ofFiber_class_mem (ζ : solutionExtFiber t f G c) :
    extOne_comap t f
        ((extensionEquiv (f ≫ t) G).symm (extensionEquiv (f ≫ t) G ζ.val)) =
      extOne_map (cPull t f c) (selfExtensionClass t) := sorry

/-- Reconstruct a solution class from a compatible relative algebra extension class. -/
def ofFiber (ζ : solutionExtFiber t f G c) : IsoClass t f G c :=
  let P := fun q : IsoClass (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G) ↦
    extOne_comap t f ((extensionEquiv (f ≫ t) G).symm q) =
      extOne_map (cPull t f c) (selfExtensionClass t)
  (Quotient.hrecOn (motive := fun q ↦ P q → IsoClass t f G c)
    (extensionEquiv (f ≫ t) G ζ.val)
    (fun SB h ↦ isoClassMk (ofCompatibleIdentitySolution t f G c SB h))
    (by exact ofCompatibleIdentitySolution_congr t f G c))
    (by exact ofFiber_class_mem t f G c ζ)

/-- The forgetful Ext¹ class of a reconstructed solution recovers the fibre element. -/
theorem toExtClass_ofFiber (ζ : solutionExtFiber t f G c) :
    toExtClass t f G c (ofFiber t f G c ζ) = ζ.val := sorry

/-- The class of the underlying extension of a solution lies in the prescribed fibre. -/
theorem toExtClass_mem (p : IsoClass t f G c) :
    extOne_comap t f (toExtClass t f G c p) =
      extOne_map (cPull t f c) (selfExtensionClass t) := sorry

/-- Reconstructing the extension class of a solution recovers its isomorphism class. -/
theorem ofFiber_toExtClass (p : IsoClass t f G c) :
    ofFiber t f G c ⟨toExtClass t f G c p, toExtClass_mem t f G c p⟩ = p := sorry

/-- Solution classes are canonically equivalent to the Ext¹ fibre over the tautological class. -/
def isoClassFiberEquiv : IsoClass t f G c ≃ solutionExtFiber t f G c where
  toFun p := ⟨toExtClass t f G c p, toExtClass_mem t f G c p⟩
  invFun := ofFiber t f G c
  left_inv := ofFiber_toExtClass t f G c
  right_inv ζ := Subtype.ext (toExtClass_ofFiber t f G c ζ)

/-- The fibre equivalence sends a solution class to its Ext¹ class. -/
theorem isoClassFiberEquiv_apply (p : IsoClass t f G c) :
    (isoClassFiberEquiv t f G c p).val = toExtClass t f G c p := sorry

/-- The inverse fibre equivalence reconstructs the solution class. -/
theorem isoClassFiberEquiv_symm_apply (ζ : solutionExtFiber t f G c) :
    (isoClassFiberEquiv t f G c).symm ζ = ofFiber t f G c ζ := sorry

/-- Solutions exist if and only if the prescribed Ext¹ fibre is nonempty. -/
theorem isoClassFiberEquiv_nonempty_iff :
    Nonempty (IsoClass t f G c) ↔ Nonempty (solutionExtFiber t f G c) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
