module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The non-triangulated eta counterexample

This file owns the explicit two-term triangle used to show that the
Berthelot--Ogus eta operator need not preserve distinguished triangles.  The
carrier objects and all three maps are concrete; only closure, commutativity,
and distinguishedness assertions are deferred as proposition-valued proof
obligations.

@stack 0GSN
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated ComplexShape HomologicalComplex ZeroObject
open scoped nonZeroDivisors

noncomputable section

universe u

namespace CochainComplex.BerthelotOgus.Int.Counterexample

variable {A : Type u} [CommRing A]

/-- The property of `A`-modules on which multiplication by `f` is injective. -/
@[stacks 0GSN "f-torsion-free module property"]
abbrev moduleProperty (f : A) : ObjectProperty (ModuleCat.{u} A) :=
  fun M ↦ IsSMulRegular M f

/-- The `f`-torsion-free module property is invariant under isomorphism. -/
@[stacks 0GSN "isomorphism invariance of the torsion-free module property", instance]
instance moduleProperty_isClosedUnderIsomorphisms (f : A) :
    (moduleProperty f).IsClosedUnderIsomorphisms := sorry

/-- The ambient zero module satisfies the `f`-torsion-free property. -/
theorem zero_mem (f : A) : moduleProperty f (0 : ModuleCat.{u} A) := sorry

/-- The `f`-torsion-free module property contains the explicit ambient zero object. -/
@[stacks 0GSN "zero object in the torsion-free module property", instance]
instance moduleProperty_containsZero (f : A) :
    (moduleProperty f).ContainsZero :=
  ⟨⟨0, isZero_zero (ModuleCat.{u} A), zero_mem f⟩⟩

/-- The `f`-torsion-free module property is closed under binary products. -/
@[stacks 0GSN "binary products of torsion-free modules", instance]
instance moduleProperty_isClosedUnderBinaryProducts (f : A) :
    (moduleProperty f).IsClosedUnderBinaryProducts := sorry

/-- The full subcategory of `f`-torsion-free `A`-modules. -/
@[stacks 0GSN "category of f-torsion-free modules"]
abbrev ModuleCategory (f : A) := (moduleProperty f).FullSubcategory

/-- Binary products in the `f`-torsion-free full subcategory are biproducts. -/
@[stacks 0GSN "binary biproducts in the torsion-free module category", instance]
instance moduleCategory_hasBinaryBiproducts (f : A) :
    HasBinaryBiproducts (ModuleCategory f) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The homotopy category of cochain complexes of `f`-torsion-free modules. -/
@[stacks 0GSN "homotopy category of f-torsion-free modules"]
abbrev KCategory (f : A) :=
  HomotopyCategory (ModuleCategory f) (ComplexShape.up ℤ)

/-- The functor forgetting `f`-torsion-freeness on homotopy categories. -/
@[stacks 0GSN "inclusion into the ambient module homotopy category"]
abbrev inclusion (f : A) :
    KCategory f ⥤ HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ) :=
  ((moduleProperty f).ι).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The principal ideal `(f)` as an `A`-module. -/
@[stacks 0GSN "principal-ideal module in the eta counterexample"]
abbrev idealObject (f : A) : ModuleCat.{u} A := ModuleCat.of A (principalIdeal f)

/-- Multiplication by `f`, with codomain the principal ideal `(f)`. -/
@[stacks 0GSN "multiplication into the principal ideal"]
abbrev idealMul (f : A) : ModuleCat.of A A ⟶ idealObject f :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton A (idealObject f)
      (⟨f, Ideal.subset_span (Set.mem_singleton f)⟩ : idealObject f))

/-- Multiplication by `f` on the principal ideal `(f)`. -/
@[stacks 0GSN "multiplication on the principal ideal"]
abbrev idealSelfMul (f : A) : idealObject f ⟶ idealObject f :=
  ModuleCat.ofHom (f • LinearMap.id)

/-- Multiplication by a nonzerodivisor identifies `A` bijectively with `(f)`. -/
theorem idealMul_bijective (f : A) (hf : f ∈ nonZeroDivisors A) :
    Function.Bijective (idealMul f).hom := sorry

/-- The canonical module isomorphism `A ≅ (f)` induced by multiplication by `f`. -/
@[stacks 0GSN "multiplication identifies A with its principal ideal"]
noncomputable def idealMulIso (f : A) (hf : f ∈ nonZeroDivisors A) :
    ModuleCat.of A A ≅ idealObject f :=
  (LinearEquiv.ofBijective (idealMul f).hom (idealMul_bijective f hf)).toModuleIso

/-- The forward map of `idealMulIso` is multiplication by `f`. -/
@[stacks 0GSN "forward map of the principal-ideal isomorphism"]
theorem idealMulIso_hom (f : A) (hf : f ∈ nonZeroDivisors A) :
    (idealMulIso f hf).hom = idealMul f := sorry

/-- The chosen inverse of `idealMulIso` is characterized by multiplication back into `(f)`. -/
theorem idealMulIso_inv_spec (f : A) (hf : f ∈ nonZeroDivisors A)
    (x : idealObject f) :
    (idealMul f).hom ((idealMulIso f hf).inv.hom x) = x := sorry

/-- The free rank-one module satisfies the `f`-torsion-free property. -/
theorem sourceModule_mem (f : A) (hf : f ∈ nonZeroDivisors A) :
    moduleProperty f (ModuleCat.of A A) := sorry

/-- The principal ideal `(f)` satisfies the `f`-torsion-free property. -/
theorem idealModule_mem (f : A) (hf : f ∈ nonZeroDivisors A) :
    moduleProperty f (idealObject f) := sorry

/-- The free rank-one module in the `f`-torsion-free full subcategory. -/
@[stacks 0GSN "rank-one source object of the eta counterexample"]
def sourceModule (f : A) (hf : f ∈ nonZeroDivisors A) : ModuleCategory f :=
  ⟨ModuleCat.of A A, sourceModule_mem f hf⟩

/-- The principal ideal in the `f`-torsion-free full subcategory. -/
@[stacks 0GSN "principal-ideal object of the eta counterexample"]
def idealModule (f : A) (hf : f ∈ nonZeroDivisors A) : ModuleCategory f :=
  ⟨idealObject f, idealModule_mem f hf⟩

/-- Multiplication `A ⟶ (f)` in the `f`-torsion-free full subcategory. -/
@[stacks 0GSN "multiplication map in the torsion-free subcategory"]
abbrev idealMulHom (f : A) (hf : f ∈ nonZeroDivisors A) :
    sourceModule f hf ⟶ idealModule f hf :=
  (moduleProperty f).homMk (idealMul f)

/-- Multiplication by `f` on `(f)` in the torsion-free full subcategory. -/
@[stacks 0GSN "principal-ideal self-map in the torsion-free subcategory"]
abbrev idealSelfMulHom (f : A) (hf : f ∈ nonZeroDivisors A) :
    idealModule f hf ⟶ idealModule f hf :=
  (moduleProperty f).homMk (idealSelfMul f)

/-- The relation `0 ⟶ 1` in the cochain complex shape. -/
theorem rel : (ComplexShape.up ℤ).Rel (0 : ℤ) 1 := sorry

/-- The two active degrees of the counterexample complex are distinct. -/
theorem zero_ne_one : (0 : ℤ) ≠ 1 := sorry

/-- The shift index used in the final vertex is `1 + 0 = 1`. -/
theorem one_add_zero : (1 : ℤ) + 0 = 1 := sorry

/-- The first displayed eta-image complex, concentrated in degree `1` with value `(f)`. -/
@[stacks 0GSN "first complex in the eta counterexample"]
abbrev idealComplex (f : A) (hf : f ∈ nonZeroDivisors A) :
    CochainComplex (ModuleCategory f) ℤ :=
  (CochainComplex.singleFunctor (ModuleCategory f) (1 : ℤ)).obj (idealModule f hf)

/-- The two-term complex `A ⟶ (f)` in degrees `0` and `1`. -/
@[stacks 0GSN "cone complex in the eta counterexample"]
abbrev coneComplex (f : A) (hf : f ∈ nonZeroDivisors A) :
    CochainComplex (ModuleCategory f) ℤ :=
  double (idealMulHom f hf) rel

/-- The shifted source complex, concentrated in degree `0` with value `A`. -/
@[stacks 0GSN "shifted source complex in the eta counterexample"]
abbrev shiftedSourceComplex (f : A) (hf : f ∈ nonZeroDivisors A) :
    CochainComplex (ModuleCategory f) ℤ :=
  (CochainComplex.singleFunctor (ModuleCategory f) (0 : ℤ)).obj (sourceModule f hf)

/-- The component defining the map from the degree-`1` single complex to the cone. -/
@[stacks 0GSN "second component of the eta counterexample triangle"]
abbrev secondComponent (f : A) (hf : f ∈ nonZeroDivisors A) :
    idealModule f hf ⟶ (coneComplex f hf).X 1 :=
  (doubleXIso₁ (idealMulHom f hf) rel zero_ne_one).inv

/-- The second component satisfies the chain-map relation. -/
theorem secondComponent_comm (f : A) (hf : f ∈ nonZeroDivisors A)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel (1 : ℤ) i) :
    secondComponent f hf ≫ (coneComplex f hf).d 1 i = 0 := sorry

/-- The map from the degree-`1` single complex into the two-term cone. -/
@[stacks 0GSN "second map of the eta counterexample triangle"]
noncomputable abbrev secondMap (f : A) (hf : f ∈ nonZeroDivisors A) :
    idealComplex f hf ⟶ coneComplex f hf :=
  mkHomFromSingle (secondComponent f hf) (secondComponent_comm f hf)

/-- The component defining the map from the cone to the shifted source. -/
@[stacks 0GSN "third component of the eta counterexample triangle"]
abbrev thirdComponent (f : A) (hf : f ∈ nonZeroDivisors A) :
    (coneComplex f hf).X 0 ⟶ sourceModule f hf :=
  -(doubleXIso₀ (idealMulHom f hf) rel).hom

/-- The third component satisfies the chain-map relation. -/
theorem thirdComponent_comm (f : A) (hf : f ∈ nonZeroDivisors A)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i (0 : ℤ)) :
    (coneComplex f hf).d i 0 ≫ thirdComponent f hf = 0 := sorry

/-- The map from the two-term cone to the shifted source complex. -/
@[stacks 0GSN "third map of the eta counterexample triangle"]
noncomputable abbrev thirdMap (f : A) (hf : f ∈ nonZeroDivisors A) :
    coneComplex f hf ⟶ shiftedSourceComplex f hf :=
  mkHomToSingle (thirdComponent f hf) (thirdComponent_comm f hf)

/-- The shifted-source identification used for the last morphism of the triangle. -/
@[stacks 0GSN "shift identification in the eta counterexample triangle"]
noncomputable def shiftIso (f : A) (hf : f ∈ nonZeroDivisors A) :
    (HomotopyCategory.singleFunctor (ModuleCategory f) (0 : ℤ)).obj
        (sourceModule f hf) ≅
      ((HomotopyCategory.singleFunctor (ModuleCategory f) (1 : ℤ)).obj
        (idealModule f hf))⟦(1 : ℤ)⟧ :=
  ((HomotopyCategory.singleFunctor (ModuleCategory f) (0 : ℤ)).mapIso
      ((moduleProperty f).isoMk (X := sourceModule f hf) (Y := idealModule f hf)
        (idealMulIso f hf))) ≪≫
    (((HomotopyCategory.singleFunctors (ModuleCategory f)).shiftIso
      (1 : ℤ) (0 : ℤ) (1 : ℤ) one_add_zero).symm.app (idealModule f hf))

/-- Example 15.96.1: the explicit eta-image triangle in the homotopy category of
`f`-torsion-free modules. -/
@[stacks 0GSN "explicit eta-image triangle"]
noncomputable def triangle (f : A) (hf : f ∈ nonZeroDivisors A) :
    Triangle (KCategory f) :=
  Triangle.mk
    ((HomotopyCategory.singleFunctor (ModuleCategory f) (1 : ℤ)).map
      (idealSelfMulHom f hf))
    ((HomotopyCategory.quotient (ModuleCategory f)
      (ComplexShape.up ℤ)).map (secondMap f hf))
    (((HomotopyCategory.quotient (ModuleCategory f)
      (ComplexShape.up ℤ)).map (thirdMap f hf)) ≫ (shiftIso f hf).hom)

/-- The image of the counterexample triangle in the ambient module homotopy category. -/
@[stacks 0GSN "ambient image of the eta counterexample triangle"]
noncomputable abbrev imageTriangle (f : A) (hf : f ∈ nonZeroDivisors A) :
    Triangle (HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
  (inclusion f).mapTriangle.obj (triangle f hf)

/-- Example 15.96.1: distinguishedness of the eta-image triangle forces `f` to be a unit. -/
@[stacks 0GSN "distinguished eta image forces the parameter to be a unit"]
theorem distinguished_implies_isUnit (f : A) (hf : f ∈ nonZeroDivisors A)
    (hT : triangle f hf ∈ distTriang (KCategory f)) : IsUnit f := sorry

/-- Example 15.96.1: for a nonunit nonzerodivisor, the explicit eta-image triangle is not
distinguished. -/
@[stacks 0GSN "eta does not preserve the displayed distinguished triangle"]
theorem not_distinguished (f : A) (hf : f ∈ nonZeroDivisors A)
    (hunit : ¬ IsUnit f) : triangle f hf ∉ distTriang (KCategory f) := sorry

/-- The ambient image of the counterexample triangle is likewise not distinguished. -/
@[stacks 0GSN "ambient eta-image triangle is not distinguished"]
theorem image_not_distinguished (f : A) (hf : f ∈ nonZeroDivisors A)
    (hunit : ¬ IsUnit f) :
    imageTriangle f hf ∉
      distTriang (HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ)) := sorry

end CochainComplex.BerthelotOgus.Int.Counterexample
