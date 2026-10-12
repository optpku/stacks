/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Prod
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext
public import ReasLib.CategoryTheory.Abelian.Projective.Ext.Linear

/-!
# The nodal ideal-power Ext counterexample

This file owns the explicit periodic ambient resolution, the finite-stage resolution windows,
and the resulting degree-two Ext models for `k[[x, y]] / (x * y)`.

@stack 0EH2
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open IadicFiniteModuleSystem.Ext
open MvPowerSeries

noncomputable section

universe u

namespace IadicFiniteModuleSystem.Ext.Nodal

/-- The two-variable formal power series ring `k[[x, y]]`. -/
@[stacks 0EH2 "two-variable formal power series ring in the nodal example"]
abbrev PowerSeriesRing (k : Type u) [Field k] : Type u :=
  MvPowerSeries (Fin 2) k

/-- The nodal relation `x * y` inside `k[[x, y]]`. -/
@[stacks 0EH2 "nodal relation"]
abbrev relation (k : Type u) [Field k] : PowerSeriesRing k :=
  X (0 : Fin 2) * X (1 : Fin 2)

/-- The nodal complete local ring `k[[x, y]] / (x * y)`. -/
@[stacks 0EH2 "nodal complete local ring"]
abbrev Ring (k : Type u) [Field k] : Type u :=
  PowerSeriesRing k ⧸ Ideal.span ({relation k} : Set (PowerSeriesRing k))

/-- The image of `x` in the nodal ring. -/
@[stacks 0EH2 "first nodal coordinate"]
abbrev x (k : Type u) [Field k] : Ring k :=
  Ideal.Quotient.mk _ (X (0 : Fin 2))

/-- The image of `y` in the nodal ring. -/
@[stacks 0EH2 "second nodal coordinate"]
abbrev y (k : Type u) [Field k] : Ring k :=
  Ideal.Quotient.mk _ (X (1 : Fin 2))

/-- The ideal `(x)` in the nodal ring. -/
@[stacks 0EH2 "distinguished ideal in the nodal counterexample"]
abbrev idealX (k : Type u) [Field k] : Ideal (Ring k) :=
  Ideal.span ({x k} : Set (Ring k))

/-- The ideal `(y)` in the nodal ring. -/
@[stacks 0EH2 "second coordinate ideal in the nodal example"]
abbrev idealY (k : Type u) [Field k] : Ideal (Ring k) :=
  Ideal.span ({y k} : Set (Ring k))

/-- The source module `M = A / (y)`; the final counterexample specializes the target to `N = M`. -/
@[stacks 0EH2 "module in the nodal Ext counterexample"]
abbrev quotientModule (k : Type u) [Field k] : ModuleCat (Ring k) :=
  ModuleCat.of (Ring k) ((Ring k) ⧸ idealY k)

/-- The nodal coordinates satisfy the defining relation `x * y = 0`. -/
@[simp, stacks 0EH2 "defining relation in the nodal ring"]
theorem x_mul_y (k : Type u) [Field k] : x k * y k = 0 := sorry

/-- The nodal coordinates also satisfy the reversed defining relation `y * x = 0`. -/
@[simp, stacks 0EH2 "reversed defining relation in the nodal ring"]
theorem y_mul_x (k : Type u) [Field k] : y k * x k = 0 := sorry

/-- The regular module used in every term of the ambient periodic resolution. -/
@[stacks 0EH2 "regular module in the ambient periodic resolution"]
abbrev regularModule (k : Type u) [Field k] : ModuleCat (Ring k) :=
  ModuleCat.of (Ring k) (Ring k)

/-- Multiplication by `x` on the regular nodal-ring module. -/
@[stacks 0EH2 "multiplication by x in the ambient periodic resolution"]
abbrev mulX (k : Type u) [Field k] : regularModule k ⟶ regularModule k :=
  ModuleCat.ofHom (LinearMap.mulLeft (Ring k) (x k))

/-- Multiplication by `y` on the regular nodal-ring module. -/
@[stacks 0EH2 "multiplication by y in the ambient periodic resolution"]
abbrev mulY (k : Type u) [Field k] : regularModule k ⟶ regularModule k :=
  ModuleCat.ofHom (LinearMap.mulLeft (Ring k) (y k))

/-- Consecutive `x`-then-`y` differentials in the periodic resolution compose to zero. -/
theorem mulX_comp_mulY (k : Type u) [Field k] : mulX k ≫ mulY k = 0 := sorry

/-- Consecutive `y`-then-`x` differentials in the periodic resolution compose to zero. -/
theorem mulY_comp_mulX (k : Type u) [Field k] : mulY k ≫ mulX k = 0 := sorry

/-- Related degrees in the downward natural-number complex have opposite parity. -/
theorem ambientResolutionParity (i j : ℕ) (h : (ComplexShape.down ℕ).Rel i j) :
    Odd (i + j) := sorry

/-- The explicit periodic chain complex
`⋯ ⟶ A ⟶[y] A ⟶[x] A ⟶[y] A` resolving `A / (y)`. -/
@[stacks 0EH2 "ambient periodic resolution complex"]
noncomputable def ambientResolutionComplex (k : Type u) [Field k] :
    ChainComplex (ModuleCat (Ring k)) ℕ :=
  HomologicalComplex.alternatingConst (regularModule k)
    (mulX_comp_mulY k) (mulY_comp_mulX k)
    ambientResolutionParity

/-- The quotient map at degree zero of the ambient periodic resolution. -/
@[stacks 0EH2 "ambient periodic resolution augmentation map"]
abbrev ambientQuotient (k : Type u) [Field k] : regularModule k ⟶ quotientModule k :=
  ModuleCat.ofHom (Submodule.mkQ (idealY k : Submodule (Ring k) (Ring k)))

/-- The differential entering degree zero is killed by the quotient augmentation. -/
theorem ambientAugmentationCondition (k : Type u) [Field k] :
    (ambientResolutionComplex k).d 1 0 ≫ ambientQuotient k = 0 := sorry

/-- The explicit augmentation of the ambient periodic complex to `A / (y)`. -/
@[stacks 0EH2 "ambient periodic resolution augmentation"]
noncomputable def ambientAugmentation (k : Type u) [Field k] :
    ambientResolutionComplex k ⟶
      (ChainComplex.single₀ (ModuleCat (Ring k))).obj (quotientModule k) :=
  (ChainComplex.toSingle₀Equiv (ambientResolutionComplex k) (quotientModule k)).symm
    ⟨ambientQuotient k, ambientAugmentationCondition k⟩

/-- The ambient periodic augmentation is a free resolution of `A / (y)`. -/
@[stacks 0EH2 "ambient periodic free resolution"]
theorem ambientIsFreeResolution (k : Type u) [Field k] :
    ChainComplex.IsFreeResolution (ambientAugmentation k) := sorry

/-- The mathlib projective-resolution owner associated to the explicit ambient periodic
resolution. -/
@[stacks 0EH2 "ambient periodic projective resolution"]
noncomputable def ambientProjectiveResolution (k : Type u) [Field k] :
    ProjectiveResolution (quotientModule k) :=
  ChainComplex.IsFreeResolution.toProjectiveResolution
    (ambientAugmentation k) (h := ambientIsFreeResolution k)

/-- The enriched module-valued Hom complex attached to the ambient periodic resolution and a
target module `N`. -/
@[stacks 0EH2 "ambient periodic Hom complex"]
abbrev ambientHomComplex (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    CochainComplex (ModuleCat (Ring k)) ℤ :=
  CochainComplex.HomComplex.moduleComplex (Ring k)
    (ambientProjectiveResolution k).cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat (Ring k)) 0).obj N)

/-- Evaluation at `1` followed by the scalar-span map recovers a morphism from the regular
module. -/
theorem regularHom_evalOne_left_inv
    (k : Type u) [Field k] (N : ModuleCat (Ring k))
    (f : regularModule k ⟶ N) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton (Ring k) N (f.hom 1)) = f := sorry

/-- The scalar-span map evaluates at `1` to its defining vector. -/
theorem regularHom_evalOne_right_inv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (z : N) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (Ring k) N z)).hom 1 = z := sorry

/-- Evaluation at `1` is additive on morphisms from the regular module. -/
theorem regularHom_evalOne_map_add
    (k : Type u) [Field k] (N : ModuleCat (Ring k))
    (f g : regularModule k ⟶ N) :
    (f + g).hom 1 = f.hom 1 + g.hom 1 := sorry

/-- Evaluation at `1` respects scalar multiplication on morphisms from the regular module. -/
theorem regularHom_evalOne_map_smul
    (k : Type u) [Field k] (N : ModuleCat (Ring k))
    (r : Ring k) (f : regularModule k ⟶ N) :
    (r • f).hom 1 = r • f.hom 1 := sorry

/-- The canonical linear equivalence `Hom_A(A, N) ≃ N`, given by evaluation at `1`. -/
@[stacks 0EH2 "evaluation equivalence for the ambient regular module"]
noncomputable def regularHomEquiv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (regularModule k ⟶ N) ≃ₗ[Ring k] N where
  toFun f := f.hom 1
  invFun z := ModuleCat.ofHom (LinearMap.toSpanSingleton (Ring k) N z)
  left_inv := regularHom_evalOne_left_inv k N
  right_inv := regularHom_evalOne_right_inv k N
  map_add' := regularHom_evalOne_map_add k N
  map_smul' := regularHom_evalOne_map_smul k N

/-- The degree identity selecting the unique component of a cochain into a complex concentrated
in degree zero. -/
theorem ambientCochainDegree_add (m : ℕ) :
    -(m : ℤ) + (m : ℤ) = 0 := sorry

/-- Every term of the chosen ambient projective resolution is the regular module. -/
theorem ambientProjectiveTerm_eq_regular
    (k : Type u) [Field k] (m : ℕ) :
    (ambientProjectiveResolution k).complex.X m = regularModule k := sorry

/-- The canonical identification of an ambient projective-resolution term with the regular
module. -/
@[stacks 0EH2 "regular terms of the ambient periodic projective resolution"]
noncomputable def ambientProjectiveTermIso
    (k : Type u) [Field k] (m : ℕ) :
    (ambientProjectiveResolution k).complex.X m ≅ regularModule k :=
  eqToIso (ambientProjectiveTerm_eq_regular k m)

/-- The underlying function that reads a degree-`m` enriched cochain as a morphism from the
regular module. -/
@[stacks 0EH2 "underlying evaluation map for an ambient Hom-complex degree"]
noncomputable def ambientCochainToRegularFun
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (ambientHomComplex k N).X (m : ℤ) → (regularModule k ⟶ N) :=
  fun z ↦
    (ambientProjectiveTermIso k m).inv ≫
      ((ambientProjectiveResolution k).cochainComplexXIso (-(m : ℤ)) m rfl).inv ≫
        CochainComplex.HomComplex.Cochain.toSingleEquiv
          (ambientCochainDegree_add m) z

/-- Reading an ambient Hom-complex degree as a regular-module morphism is additive. -/
theorem ambientCochainToRegularFun_map_add
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ)
    (z w : (ambientHomComplex k N).X (m : ℤ)) :
    ambientCochainToRegularFun k N m (z + w) =
      ambientCochainToRegularFun k N m z + ambientCochainToRegularFun k N m w := sorry

/-- Reading an ambient Hom-complex degree as a regular-module morphism is linear. -/
theorem ambientCochainToRegularFun_map_smul
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ)
    (r : Ring k) (z : (ambientHomComplex k N).X (m : ℤ)) :
    ambientCochainToRegularFun k N m (r • z) =
      r • ambientCochainToRegularFun k N m z := sorry

/-- Read a degree-`m` enriched cochain linearly as a morphism from the regular module. -/
@[stacks 0EH2 "evaluation of an ambient Hom-complex degree"]
noncomputable def ambientCochainToRegular
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (ambientHomComplex k N).X (m : ℤ) →ₗ[Ring k] (regularModule k ⟶ N) where
  toFun := ambientCochainToRegularFun k N m
  map_add' := ambientCochainToRegularFun_map_add k N m
  map_smul' := ambientCochainToRegularFun_map_smul k N m

/-- The underlying function assembling a regular-module morphism into the corresponding
degree-`m` enriched cochain. -/
@[stacks 0EH2 "underlying assembly map for an ambient Hom-complex degree"]
noncomputable def regularToAmbientCochainFun
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (regularModule k ⟶ N) → (ambientHomComplex k N).X (m : ℤ) :=
  fun f ↦
    (CochainComplex.HomComplex.Cochain.toSingleEquiv
      (ambientCochainDegree_add m)).symm
        (((ambientProjectiveResolution k).cochainComplexXIso
          (-(m : ℤ)) m rfl).hom ≫ (ambientProjectiveTermIso k m).hom ≫ f)

/-- Assembly of regular-module morphisms into enriched cochains is additive. -/
theorem regularToAmbientCochainFun_map_add
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ)
    (f g : regularModule k ⟶ N) :
    regularToAmbientCochainFun k N m (f + g) =
      regularToAmbientCochainFun k N m f + regularToAmbientCochainFun k N m g := sorry

/-- Assembly of regular-module morphisms into enriched cochains is linear. -/
theorem regularToAmbientCochainFun_map_smul
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ)
    (r : Ring k) (f : regularModule k ⟶ N) :
    regularToAmbientCochainFun k N m (r • f) =
      r • regularToAmbientCochainFun k N m f := sorry

/-- Assemble a regular-module morphism linearly into the corresponding degree-`m` enriched
cochain. -/
@[stacks 0EH2 "assembly of an ambient Hom-complex degree"]
noncomputable def regularToAmbientCochain
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (regularModule k ⟶ N) →ₗ[Ring k] (ambientHomComplex k N).X (m : ℤ) where
  toFun := regularToAmbientCochainFun k N m
  map_add' := regularToAmbientCochainFun_map_add k N m
  map_smul' := regularToAmbientCochainFun_map_smul k N m

/-- Assembly after evaluation is the identity on an ambient Hom-complex degree. -/
theorem regularToAmbientCochain_ambientCochainToRegular
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ)
    (z : (ambientHomComplex k N).X (m : ℤ)) :
    regularToAmbientCochain k N m (ambientCochainToRegular k N m z) = z := sorry

/-- Evaluation after assembly is the identity on regular-module morphisms. -/
theorem ambientCochainToRegular_regularToAmbientCochain
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ)
    (f : regularModule k ⟶ N) :
    ambientCochainToRegular k N m (regularToAmbientCochain k N m f) = f := sorry

/-- Degree-`m` enriched cochains are canonically equivalent to morphisms from the regular
module. -/
@[stacks 0EH2 "regular-module form of an ambient Hom-complex degree"]
noncomputable def ambientCochainRegularEquiv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (ambientHomComplex k N).X (m : ℤ) ≃ₗ[Ring k] (regularModule k ⟶ N) where
  toFun := ambientCochainToRegular k N m
  invFun := regularToAmbientCochain k N m
  left_inv := regularToAmbientCochain_ambientCochainToRegular k N m
  right_inv := ambientCochainToRegular_regularToAmbientCochain k N m
  map_add' := (ambientCochainToRegular k N m).map_add
  map_smul' := (ambientCochainToRegular k N m).map_smul

/-- Each nonnegative degree of the ambient enriched Hom complex is canonically `N`. -/
@[stacks 0EH2 "terms of the ambient enriched Hom complex"]
noncomputable def ambientHomDegreeEquiv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (ambientHomComplex k N).X (m : ℤ) ≃ₗ[Ring k] N :=
  (ambientCochainRegularEquiv k N m).trans (regularHomEquiv k N)

/-- The module-category isomorphism underlying the degreewise ambient Hom-complex
identification. -/
@[stacks 0EH2 "module terms of the ambient enriched Hom complex"]
noncomputable def ambientHomDegreeIso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (m : ℕ) :
    (ambientHomComplex k N).X (m : ℤ) ≅ N :=
  (ambientHomDegreeEquiv k N m).toModuleIso

/-- The actual degree-two short window of the enriched Hom complex. -/
@[stacks 0EH2 "degree-two window of the ambient Hom complex"]
noncomputable abbrev ambientHomExt2Window
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    ShortComplex (ModuleCat (Ring k)) :=
  (ambientProjectiveResolution k).extHomWindow N 2

/-- The canonical linear computation of ambient Ext as homology of the enriched Hom complex
associated to the explicit periodic projective resolution. -/
@[stacks 0EH2 "ambient Ext computation from the periodic resolution"]
noncomputable def ambientExtComputation
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    Ext (quotientModule k) N 2 ≃ₗ[Ring k]
      (ambientHomExt2Window k N).homology :=
  (ambientProjectiveResolution k).extLinearEquivWindowHomology

/-- The numerator `N[y]` in the ambient `Ext²` computation, for an arbitrary target module
`N`. -/
@[stacks 0EH2 "y-torsion numerator in the ambient second Ext computation"]
abbrev yTorsion (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    Submodule (Ring k) N :=
  Submodule.torsionBy (Ring k) N (y k)

/-- Multiplication by `y` vanishes on the distinguished quotient module `A / (y)`. -/
@[stacks 0EH2 "y acts trivially on the nodal quotient module"]
theorem y_smul_quotientModule_eq_zero
    (k : Type u) [Field k] (z : quotientModule k) :
    y k • z = 0 := sorry

/-- Every element of `A / (y)` is killed by `y`. -/
@[stacks 0EH2 "y-torsion of the nodal quotient module"]
theorem yTorsion_quotientModule_eq_top (k : Type u) [Field k] :
    yTorsion k (quotientModule k) = ⊤ := sorry

/-- The submodule `xN` in the ambient `Ext²` computation. -/
@[stacks 0EH2 "x-multiples in the ambient second Ext computation"]
abbrev xMultiples (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    Submodule (Ring k) N :=
  idealX k • (⊤ : Submodule (Ring k) N)

/-- The relation `x * y = 0` places `xN` inside the `y`-torsion of every nodal-ring module. -/
@[stacks 0EH2 "x-multiples lie in y-torsion"]
theorem xMultiples_le_yTorsion (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    xMultiples k N ≤ yTorsion k N := sorry

/-- Scalar multiplication by `x` followed by scalar multiplication by `y` is zero on `N`. -/
theorem ambientExt2Differentials_zero
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (DistribSMul.toLinearMap (Ring k) N (y k)).comp
      (DistribSMul.toLinearMap (Ring k) N (x k)) = 0 := sorry

/-- The degree-two cochain window `N ⟶[x] N ⟶[y] N` obtained from the ambient periodic
resolution. -/
@[stacks 0EH2 "ambient degree-two Ext cochain window"]
def ambientExt2Window (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    ShortComplex (ModuleCat (Ring k)) :=
  ShortComplex.moduleCatMk
    (DistribSMul.toLinearMap (Ring k) N (x k))
    (DistribSMul.toLinearMap (Ring k) N (y k))
    (ambientExt2Differentials_zero k N)

/-- The left object of the degree-two Hom window is its degree-one term. -/
theorem ambientHomWindowX1_eq
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).X₁ = (ambientHomComplex k N).X (1 : ℤ) := sorry

/-- The middle object of the degree-two Hom window is its degree-two term. -/
theorem ambientHomWindowX2_eq
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).X₂ = (ambientHomComplex k N).X (2 : ℤ) := sorry

/-- The right object of the degree-two Hom window is its degree-three term. -/
theorem ambientHomWindowX3_eq
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).X₃ = (ambientHomComplex k N).X (3 : ℤ) := sorry

/-- The left component of the explicit ambient window identification. -/
@[stacks 0EH2 "left component of the ambient Ext window identification"]
noncomputable def ambientWindowX1Iso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).X₁ ≅ N :=
  eqToIso (ambientHomWindowX1_eq k N) ≪≫ ambientHomDegreeIso k N 1

/-- The middle component of the explicit ambient window identification. -/
@[stacks 0EH2 "middle component of the ambient Ext window identification"]
noncomputable def ambientWindowX2Iso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).X₂ ≅ N :=
  eqToIso (ambientHomWindowX2_eq k N) ≪≫ ambientHomDegreeIso k N 2

/-- The right component of the explicit ambient window identification. -/
@[stacks 0EH2 "right component of the ambient Ext window identification"]
noncomputable def ambientWindowX3Iso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).X₃ ≅ N :=
  eqToIso (ambientHomWindowX3_eq k N) ≪≫ ambientHomDegreeIso k N 3

/-- Evaluation at `1` identifies the first enriched Hom differential with multiplication by
`x`. -/
theorem ambientWindowIso_comm_f
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientWindowX1Iso k N).hom ≫ (ambientExt2Window k N).f =
      (ambientHomExt2Window k N).f ≫ (ambientWindowX2Iso k N).hom := sorry

/-- Evaluation at `1` identifies the second enriched Hom differential with multiplication by
`y`. -/
theorem ambientWindowIso_comm_g
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientWindowX2Iso k N).hom ≫ (ambientExt2Window k N).g =
      (ambientHomExt2Window k N).g ≫ (ambientWindowX3Iso k N).hom := sorry

/-- The degree-two enriched Hom window is canonically the explicit scalar-multiplication window
`N ⟶[x] N ⟶[y] N`. -/
@[stacks 0EH2 "explicit form of the ambient degree-two Hom window"]
noncomputable def ambientWindowIso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    ambientHomExt2Window k N ≅ ambientExt2Window k N :=
  ShortComplex.isoMk (ambientWindowX1Iso k N)
    (ambientWindowX2Iso k N) (ambientWindowX3Iso k N)
    (ambientWindowIso_comm_f k N) (ambientWindowIso_comm_g k N)

/-- The homology isomorphism induced by the explicit identification of the two degree-two
windows. -/
@[stacks 0EH2 "homology comparison for the ambient degree-two Hom window"]
noncomputable def ambientWindowHomologyIso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).homology ≅ (ambientExt2Window k N).homology :=
  ShortComplex.homologyMapIso (ambientWindowIso k N)

/-- The linear equivalence underlying the ambient degree-two window comparison in homology. -/
@[stacks 0EH2 "linear homology comparison for the ambient degree-two Hom window"]
noncomputable def ambientWindowHomologyEquiv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientHomExt2Window k N).homology ≃ₗ[Ring k]
      (ambientExt2Window k N).homology :=
  (ambientWindowHomologyIso k N).toLinearEquiv

/-- The boundary map `N ⟶ N[y]` induced by multiplication by `x`. -/
@[stacks 0EH2 "boundary map in the ambient second Ext computation"]
abbrev ambientBoundaryMap (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    N →ₗ[Ring k] yTorsion k N :=
  (ambientExt2Window k N).moduleCatToCycles

/-- The submodule of degree-two boundaries inside `N[y]`. -/
@[stacks 0EH2 "boundaries in the ambient second Ext computation"]
abbrev ambientBoundaries (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    Submodule (Ring k) (yTorsion k N) :=
  LinearMap.range (ambientBoundaryMap k N)

/-- The degree-two boundaries agree with `xN`, viewed inside `N[y]`. -/
@[stacks 0EH2 "ambient degree-two boundaries are x-multiples"]
theorem ambientBoundaries_eq_comap_xMultiples
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    ambientBoundaries k N = (xMultiples k N).comap (yTorsion k N).subtype := sorry

/-- The source-faithful model `N[y] / xN` for the ambient second Ext group, expressed as
cycles modulo boundaries. -/
@[stacks 0EH2 "torsion quotient model for the ambient second Ext group"]
abbrev Ext2Model (k : Type u) [Field k] (N : ModuleCat (Ring k)) : Type u :=
  yTorsion k N ⧸ ambientBoundaries k N

/-- The canonical homology object of the ambient degree-two window is the explicit model
`N[y] / xN`. -/
@[stacks 0EH2 "ambient degree-two homology model"]
noncomputable def ambientExt2HomologyIso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientExt2Window k N).homology ≅ ModuleCat.of (Ring k) (Ext2Model k N) :=
  (ambientExt2Window k N).moduleCatHomologyIso

/-- The linear equivalence underlying the ambient degree-two homology identification. -/
@[stacks 0EH2 "linear form of the ambient second Ext homology model"]
noncomputable def ambientExt2HomologyEquiv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) :
    (ambientExt2Window k N).homology ≃ₗ[Ring k] Ext2Model k N :=
  (ambientExt2HomologyIso k N).toLinearEquiv

/-- The positive quotient ring at level `n` in the nodal example. -/
@[stacks 0EH2 "positive quotient ring in the nodal example"]
abbrev StageRing (k : Type u) [Field k] (n : ℕ+) : Type u :=
  IadicFiniteModuleSystem.stageRing (Ring k) (idealX k) n

/-- The reduction `Nₙ = N / I ^ n N` of an arbitrary nodal-ring module. -/
@[stacks 0EH2 "reduced module in the nodal example"]
abbrev stageModule (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    ModuleCat (StageRing k n) :=
  Ideal.PowerQuotient.stageOver (idealX k) N (n : ℕ)

/-- The image of `x` in the positive quotient ring at level `n`. -/
@[stacks 0EH2 "first coordinate at a reduced stage"]
abbrev stageX (k : Type u) [Field k] (n : ℕ+) : StageRing k n :=
  Ideal.Quotient.mk ((idealX k) ^ (n : ℕ)) (x k)

/-- The image of `y` in the positive quotient ring at level `n`. -/
@[stacks 0EH2 "second coordinate at a reduced stage"]
abbrev stageY (k : Type u) [Field k] (n : ℕ+) : StageRing k n :=
  Ideal.Quotient.mk ((idealX k) ^ (n : ℕ)) (y k)

/-- The reduced nodal coordinates still satisfy `x * y = 0`. -/
@[simp, stacks 0EH2 "nodal relation at a reduced stage"]
theorem stageX_mul_stageY (k : Type u) [Field k] (n : ℕ+) :
    stageX k n * stageY k n = 0 := sorry

/-- The image of `x` is nilpotent of order `n` in the `n`th quotient ring. -/
@[simp, stacks 0EH2 "nilpotence of x at a reduced stage"]
theorem stageX_pow_eq_zero (k : Type u) [Field k] (n : ℕ+) :
    stageX k n ^ (n : ℕ) = 0 := sorry

/-- The principal ideal generated by the image of `x` at level `n`. -/
@[stacks 0EH2 "first coordinate ideal at a reduced stage"]
abbrev stageIdealX (k : Type u) [Field k] (n : ℕ+) : Ideal (StageRing k n) :=
  Ideal.span ({stageX k n} : Set (StageRing k n))

/-- The regular module over the `n`th quotient ring. -/
@[stacks 0EH2 "regular module at a reduced stage"]
abbrev stageRegular (k : Type u) [Field k] (n : ℕ+) : ModuleCat (StageRing k n) :=
  ModuleCat.of (StageRing k n) (StageRing k n)

/-- Multiplication by `x` on the regular module at level `n`. -/
@[stacks 0EH2 "multiplication by x at a reduced stage"]
abbrev stageResolutionMulX (k : Type u) [Field k] (n : ℕ+) :
    stageRegular k n ⟶ stageRegular k n :=
  ModuleCat.ofHom (LinearMap.mulLeft (StageRing k n) (stageX k n))

/-- Multiplication by `y` on the regular module at level `n`. -/
@[stacks 0EH2 "multiplication by y at a reduced stage"]
abbrev stageResolutionMulY (k : Type u) [Field k] (n : ℕ+) :
    stageRegular k n ⟶ stageRegular k n :=
  ModuleCat.ofHom (LinearMap.mulLeft (StageRing k n) (stageY k n))

/-- The row map `(y, x ^ (n - 1)) : Aₙ² ⟶ Aₙ` in the reduced free resolution. -/
@[stacks 0EH2 "degree-three differential in the reduced free resolution"]
abbrev stageResolutionRow (k : Type u) [Field k] (n : ℕ+) :
    ModuleCat.of (StageRing k n) (StageRing k n × StageRing k n) ⟶ stageRegular k n :=
  ModuleCat.ofHom (LinearMap.coprod
    (LinearMap.mulLeft (StageRing k n) (stageY k n))
    (LinearMap.mulLeft (StageRing k n) (stageX k n ^ n.natPred)))

/-- The row `(y, x ^ (n - 1))` followed by multiplication by `x` is zero. -/
theorem stageResolutionAtTwo_zero (k : Type u) [Field k] (n : ℕ+) :
    stageResolutionRow k n ≫ stageResolutionMulX k n = 0 := sorry

/-- The reduced resolution prefix `Aₙ² ⟶[(y, x ^ (n - 1))] Aₙ ⟶[x] Aₙ`. -/
@[stacks 0EH2 "degree-two prefix of the reduced free resolution"]
def stageResolutionAtTwo (k : Type u) [Field k] (n : ℕ+) :
    ShortComplex (ModuleCat (StageRing k n)) :=
  ShortComplex.mk (stageResolutionRow k n) (stageResolutionMulX k n)
    (stageResolutionAtTwo_zero k n)

/-- Multiplication by `x` followed by multiplication by `y` is zero at level `n`. -/
theorem stageResolutionAtOne_zero (k : Type u) [Field k] (n : ℕ+) :
    stageResolutionMulX k n ≫ stageResolutionMulY k n = 0 := sorry

/-- The reduced resolution prefix `Aₙ ⟶[x] Aₙ ⟶[y] Aₙ`. -/
@[stacks 0EH2 "degree-one prefix of the reduced free resolution"]
def stageResolutionAtOne (k : Type u) [Field k] (n : ℕ+) :
    ShortComplex (ModuleCat (StageRing k n)) :=
  ShortComplex.mk (stageResolutionMulX k n) (stageResolutionMulY k n)
    (stageResolutionAtOne_zero k n)

/-- The reduced free resolution is exact at its degree-two regular term. -/
@[stacks 0EH2 "exactness at degree two of the reduced free resolution"]
theorem stageResolutionAtTwo_exact (k : Type u) [Field k] (n : ℕ+) :
    (stageResolutionAtTwo k n).Exact := sorry

/-- The reduced free resolution is exact at its degree-one regular term. -/
@[stacks 0EH2 "exactness at degree one of the reduced free resolution"]
theorem stageResolutionAtOne_exact (k : Type u) [Field k] (n : ℕ+) :
    (stageResolutionAtOne k n).Exact := sorry

/-- Multiplication by `x` on the reduced target `Nₙ`. -/
@[stacks 0EH2 "multiplication by x on a reduced target"]
abbrev stageMulXMap
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    stageModule k N n →ₗ[StageRing k n] stageModule k N n :=
  DistribSMul.toLinearMap (StageRing k n) (stageModule k N n) (stageX k n)

/-- The pair of actions `(y, x ^ (n - 1))` on the reduced target `Nₙ`. -/
@[stacks 0EH2 "relation map on a reduced target"]
abbrev stageRelationMap
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    stageModule k N n →ₗ[StageRing k n] stageModule k N n × stageModule k N n :=
  LinearMap.prod
    (DistribSMul.toLinearMap (StageRing k n) (stageModule k N n) (stageY k n))
    (DistribSMul.toLinearMap (StageRing k n) (stageModule k N n)
      (stageX k n ^ n.natPred))

/-- The degree-two reduced cochain differentials compose to zero. -/
theorem stageExt2Differentials_zero
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    (stageRelationMap k N n).comp (stageMulXMap k N n) = 0 := sorry

/-- The degree-two cochain window
`Nₙ ⟶[x] Nₙ ⟶[(y, x ^ (n - 1))] Nₙ²` obtained from the reduced resolution. -/
@[stacks 0EH2 "reduced degree-two Ext cochain window"]
def stageExt2Window
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    ShortComplex (ModuleCat (StageRing k n)) :=
  ShortComplex.moduleCatMk (stageMulXMap k N n) (stageRelationMap k N n)
    (stageExt2Differentials_zero k N n)

/-- The cycles of the reduced degree-two cochain window. -/
@[stacks 0EH2 "cycles in the reduced second Ext computation"]
abbrev stageNumerator (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    Submodule (StageRing k n) (stageModule k N n) :=
  LinearMap.ker (stageRelationMap k N n)

/-- The reduced cycles are the intersection `Nₙ[y] ∩ Nₙ[x ^ (n - 1)]`. -/
@[stacks 0EH2 "reduced degree-two cycles as a torsion intersection"]
theorem stageNumerator_eq_torsion_inf
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    stageNumerator k N n =
      Submodule.torsionBy (StageRing k n) (stageModule k N n) (stageY k n) ⊓
        Submodule.torsionBy (StageRing k n) (stageModule k N n)
          (stageX k n ^ n.natPred) := sorry

/-- Multiplication by the stage image of `y` vanishes on the reduction of `A / (y)`. -/
@[stacks 0EH2 "y acts trivially on every reduced nodal quotient module"]
theorem stageY_smul_quotientModule_eq_zero
    (k : Type u) [Field k] (n : ℕ+)
    (z : stageModule k (quotientModule k) n) :
    stageY k n • z = 0 := sorry

/-- For the distinguished quotient module, the reduced numerator is precisely the
`x ^ (n - 1)`-torsion submodule. -/
@[stacks 0EH2 "specialized reduced numerator in the nodal counterexample"]
theorem stageNumerator_quotientModule_eq_torsion (k : Type u) [Field k] (n : ℕ+) :
    stageNumerator k (quotientModule k) n =
      Submodule.torsionBy (StageRing k n) (stageModule k (quotientModule k) n)
        (stageX k n ^ n.natPred) := sorry

/-- The specialized reduced degree-two cochain window for `A / (y)` is exact. -/
@[stacks 0EH2 "exact reduced Ext window in the nodal counterexample"]
theorem stageExt2Window_quotientModule_exact
    (k : Type u) [Field k] (n : ℕ+) :
    (stageExt2Window k (quotientModule k) n).Exact := sorry

/-- The submodule `xNₙ` in the reduced second Ext computation. -/
@[stacks 0EH2 "x-multiples in the reduced second Ext computation"]
abbrev stageXMultiples (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    Submodule (StageRing k n) (stageModule k N n) :=
  stageIdealX k n • (⊤ : Submodule (StageRing k n) (stageModule k N n))

/-- The submodule `xNₙ` lies in the torsion intersection defining the reduced numerator. -/
@[stacks 0EH2 "x-multiples lie in the reduced Ext numerator"]
theorem stageXMultiples_le_numerator
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    stageXMultiples k N n ≤ stageNumerator k N n := sorry

/-- The boundary map `Nₙ ⟶ Nₙ[y] ∩ Nₙ[x ^ (n - 1)]` induced by multiplication by `x`. -/
@[stacks 0EH2 "boundary map in the reduced second Ext computation"]
abbrev stageBoundaryMap
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    stageModule k N n →ₗ[StageRing k n] stageNumerator k N n :=
  (stageExt2Window k N n).moduleCatToCycles

/-- The submodule of boundaries in the reduced degree-two cochain window. -/
@[stacks 0EH2 "boundaries in the reduced second Ext computation"]
abbrev stageBoundaries
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    Submodule (StageRing k n) (stageNumerator k N n) :=
  LinearMap.range (stageBoundaryMap k N n)

/-- The reduced degree-two boundaries agree with `xNₙ`, viewed inside the cycles. -/
@[stacks 0EH2 "reduced degree-two boundaries are x-multiples"]
theorem stageBoundaries_eq_comap_xMultiples
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    stageBoundaries k N n =
      (stageXMultiples k N n).comap (stageNumerator k N n).subtype := sorry

/-- The source-faithful model
`(Nₙ[y] ∩ Nₙ[x ^ (n - 1)]) / xNₙ` for the reduced second Ext group. -/
@[stacks 0EH2 "torsion-intersection quotient model for reduced second Ext"]
abbrev StageExt2Model
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) : Type u :=
  stageNumerator k N n ⧸ stageBoundaries k N n

/-- The homology object of the reduced degree-two window is the explicit torsion-intersection
quotient model. -/
@[stacks 0EH2 "reduced degree-two homology model"]
noncomputable def stageExt2HomologyIso
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    (stageExt2Window k N n).homology ≅
      ModuleCat.of (StageRing k n) (StageExt2Model k N n) :=
  (stageExt2Window k N n).moduleCatHomologyIso

/-- The linear equivalence underlying the reduced degree-two homology identification. -/
@[stacks 0EH2 "linear reduced degree-two homology model"]
noncomputable def stageExt2HomologyEquiv
    (k : Type u) [Field k] (N : ModuleCat (Ring k)) (n : ℕ+) :
    (stageExt2Window k N n).homology ≃ₗ[StageRing k n] StageExt2Model k N n :=
  (stageExt2HomologyIso k N n).toLinearEquiv

variable (k : Type u) [Field k]

/-- For every target module `N`, the ambient second Ext group has the source computation
`Ext²_A(M, N) ≃ N[y] / xN`. -/
@[stacks 0EH2 "torsion quotient formula for the ambient second Ext group"]
noncomputable def ext2Formula (N : ModuleCat (Ring k)) :
    Ext (quotientModule k) N 2 ≃ₗ[Ring k] Ext2Model k N :=
  (ambientExtComputation k N).trans <|
    (ambientWindowHomologyEquiv k N).trans (ambientExt2HomologyEquiv k N)

/-- The ambient Ext formula factors through the enriched Hom window and its explicit
scalar-multiplication model. -/
@[stacks 0EH2 "factorization of the ambient second Ext formula"]
theorem ext2Formula_apply (N : ModuleCat (Ring k))
    (z : Ext (quotientModule k) N 2) :
    ext2Formula k N z =
      ambientExt2HomologyEquiv k N
        (ambientWindowHomologyEquiv k N (ambientExtComputation k N z)) := sorry

/-- The constant coefficient vanishes on the nodal relation ideal. -/
theorem relationIdeal_constantCoeff_eq_zero
    (f : PowerSeriesRing k)
    (hf : f ∈ Ideal.span ({relation k} : Set (PowerSeriesRing k))) :
    MvPowerSeries.constantCoeff f = 0 := sorry

/-- Constant coefficient on the nodal ring. -/
@[stacks 0EH2 "constant coefficient on the nodal ring"]
noncomputable def nodalConstantCoeff : Ring k →+* k :=
  Ideal.Quotient.lift _ MvPowerSeries.constantCoeff
    (relationIdeal_constantCoeff_eq_zero k)

/-- Constant coefficient on the nodal ring kills the ideal generated by `y`. -/
theorem idealY_nodalConstantCoeff_eq_zero
    (a : Ring k) (ha : a ∈ idealY k) :
    nodalConstantCoeff k a = 0 := sorry

/-- Constant coefficient on `A / (y)`. -/
@[stacks 0EH2 "constant coefficient on the nodal quotient module"]
noncomputable def quotientModuleConstantCoeff : quotientModule k →+* k :=
  Ideal.Quotient.lift _ (nodalConstantCoeff k)
    (idealY_nodalConstantCoeff_eq_zero k)

/-- Constant coefficient on `A / (y)` commutes with the `k`-action. -/
theorem quotientModuleConstantCoeff_map_smul
    (c : k) (z : quotientModule k) :
    quotientModuleConstantCoeff k (c • z) = c • quotientModuleConstantCoeff k z := sorry

/-- Constant coefficient on `A / (y)`, as a `k`-linear map. -/
@[stacks 0EH2 "linear constant coefficient on the nodal quotient module"]
noncomputable def quotientModuleConstantCoeffLinear : quotientModule k →ₗ[k] k where
  toFun := quotientModuleConstantCoeff k
  map_add' := (quotientModuleConstantCoeff k).map_add
  map_smul' := quotientModuleConstantCoeff_map_smul k

/-- Constant coefficient restricted to the `y`-torsion numerator. -/
@[stacks 0EH2 "constant coefficient on the ambient Ext numerator"]
noncomputable def yTorsionConstantCoeff :
    yTorsion k (quotientModule k) →ₗ[k] k :=
  (quotientModuleConstantCoeffLinear k).comp
    ((yTorsion k (quotientModule k)).subtype.restrictScalars k)

/-- Ambient degree-two boundaries have zero constant coefficient. -/
theorem ambientBoundaries_le_ker_yTorsionConstantCoeff :
    (ambientBoundaries k (quotientModule k)).restrictScalars k ≤
      LinearMap.ker (yTorsionConstantCoeff k) := sorry

/-- The constant-coefficient map from the explicit ambient `Ext²` quotient model to `k`. -/
@[stacks 0EH2 "constant coefficient on the ambient second Ext model"]
noncomputable def ext2ModelToBase :
    Ext2Model k (quotientModule k) →ₗ[k] k :=
  ((ambientBoundaries k (quotientModule k)).restrictScalars k).liftQ
      (yTorsionConstantCoeff k)
      (ambientBoundaries_le_ker_yTorsionConstantCoeff k) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k
      (ambientBoundaries k (quotientModule k))).symm.toLinearMap

/-- The image of a scalar constant in `A / (y)` lies in its `y`-torsion submodule. -/
theorem base_mem_yTorsion (c : k) :
    Algebra.linearMap k (quotientModule k) c ∈
      (yTorsion k (quotientModule k)).restrictScalars k := sorry

/-- Embed a scalar constant into the `y`-torsion numerator of the ambient model. -/
@[stacks 0EH2 "constant classes in the ambient Ext numerator"]
noncomputable def baseToYTorsion :
    k →ₗ[k] yTorsion k (quotientModule k) :=
  (Algebra.linearMap k (quotientModule k)).codRestrict
    ((yTorsion k (quotientModule k)).restrictScalars k)
    (base_mem_yTorsion k)

/-- Send a scalar to its constant class in the ambient `Ext²` quotient model. -/
@[stacks 0EH2 "constant classes in the ambient second Ext model"]
noncomputable def baseToExt2Model :
    k →ₗ[k] Ext2Model k (quotientModule k) :=
  ((ambientBoundaries k (quotientModule k)).mkQ.restrictScalars k) ∘ₗ
    baseToYTorsion k

/-- Taking constant coefficient after inserting a constant class is the identity. -/
theorem ext2ModelToBase_baseToExt2Model (c : k) :
    ext2ModelToBase k (baseToExt2Model k c) = c := sorry

/-- Every class in the ambient model is represented by its constant coefficient. -/
theorem baseToExt2Model_ext2ModelToBase
    (z : Ext2Model k (quotientModule k)) :
    baseToExt2Model k (ext2ModelToBase k z) = z := sorry

/-- Constant coefficient on a quotient class is constant coefficient on its representative. -/
@[stacks 0EH2 "constant coefficient formula on the ambient Ext quotient"]
theorem ext2ModelToBase_mkQ
    (z : yTorsion k (quotientModule k)) :
    ext2ModelToBase k
        ((ambientBoundaries k (quotientModule k)).mkQ z) =
      quotientModuleConstantCoeff k z := sorry

/-- A scalar is sent to its constant class in the ambient quotient model. -/
@[stacks 0EH2 "constant-class formula in the ambient Ext quotient"]
theorem baseToExt2Model_apply (c : k) :
    baseToExt2Model k c =
      (ambientBoundaries k (quotientModule k)).mkQ (baseToYTorsion k c) := sorry

/-- The ambient torsion-quotient model is canonically one-dimensional over `k`, via constant
coefficient and constant classes. -/
@[stacks 0EH2 "ambient second Ext model over the residue field"]
noncomputable def ext2ModelEquivBase :
    Ext2Model k (quotientModule k) ≃ₗ[k] k where
  toFun := ext2ModelToBase k
  invFun := baseToExt2Model k
  left_inv := baseToExt2Model_ext2ModelToBase k
  right_inv := ext2ModelToBase_baseToExt2Model k
  map_add' := (ext2ModelToBase k).map_add
  map_smul' := (ext2ModelToBase k).map_smul

/-- The ambient Ext formula respects the scalar action of the coefficient field. -/
theorem ext2Formula_map_base_smul
    (c : k) (z : Ext (quotientModule k) (quotientModule k) 2) :
    ext2Formula k (quotientModule k) (c • z) =
      c • ext2Formula k (quotientModule k) z := sorry

/-- The ambient Ext formula specialized to `A / (y)`, viewed linearly over the coefficient
field. -/
@[stacks 0EH2 "ambient second Ext model over the coefficient field"]
noncomputable def ext2FormulaOverBase :
    Ext (quotientModule k) (quotientModule k) 2 ≃ₗ[k]
      Ext2Model k (quotientModule k) where
  toFun := ext2Formula k (quotientModule k)
  invFun := (ext2Formula k (quotientModule k)).symm
  left_inv := (ext2Formula k (quotientModule k)).left_inv
  right_inv := (ext2Formula k (quotientModule k)).right_inv
  map_add' := (ext2Formula k (quotientModule k)).map_add
  map_smul' := ext2Formula_map_base_smul k

/-- The ambient second Ext group of `A / (y)` is concretely one-dimensional over `k`. -/
@[stacks 0EH2 "ambient second Ext group over the residue field"]
noncomputable def ext2EquivBase :
    Ext (quotientModule k) (quotientModule k) 2 ≃ₗ[k] k :=
  (ext2FormulaOverBase k).trans (ext2ModelEquivBase k)

/-- The concrete residue-field computation is the ambient model formula followed by constant
coefficient. -/
@[stacks 0EH2 "ambient second Ext residue-field formula"]
theorem ext2EquivBase_apply
    (z : Ext (quotientModule k) (quotientModule k) 2) :
    ext2EquivBase k z =
      ext2ModelEquivBase k (ext2Formula k (quotientModule k) z) := sorry

/-- The residue-field equivalence is given by constant coefficient. -/
@[stacks 0EH2 "ambient second Ext equivalence formula"]
theorem ext2ModelEquivBase_apply (z : Ext2Model k (quotientModule k)) :
    ext2ModelEquivBase k z = ext2ModelToBase k z := sorry

/-- The inverse residue-field equivalence sends a scalar to its constant class. -/
@[stacks 0EH2 "inverse ambient second Ext equivalence formula"]
theorem ext2ModelEquivBase_symm_apply (c : k) :
    (ext2ModelEquivBase k).symm c = baseToExt2Model k c := sorry

/-- For every target module `N`, each reduced second Ext group has the source computation
`Ext²(Mₙ, Nₙ) ≃ (Nₙ[y] ∩ Nₙ[x ^ (n - 1)]) / xNₙ`. -/
@[stacks 0EH2 "torsion-intersection formula for reduced second Ext"]
theorem stageExt2Formula (N : ModuleCat (Ring k)) (n : ℕ+) :
    IsIsomorphic
      (ModuleCat.of (StageRing k n)
        (Ext (stageModule k (quotientModule k) n) (stageModule k N n) 2))
      (ModuleCat.of (StageRing k n) (StageExt2Model k N n)) := sorry

/-- The explicit reduced second Ext model vanishes at every positive level. -/
@[stacks 0EH2 "vanishing of the reduced second Ext model"]
theorem stageExt2ModelIsZero (n : ℕ+) :
    IsZero
      (ModuleCat.of (StageRing k n) (StageExt2Model k (quotientModule k) n)) := sorry

/-- Example 15.101.10 (1): for `A = k[[x, y]] / (x * y)`, `I = (x)`, and
`M = N = A / (y)`, the ambient group `Ext²_A(M, N)` is linearly equivalent to `k`. -/
@[stacks 0EH2 "Ext counterexample for the nodal ideal-power quotients"]
noncomputable def ext2Counterexample :
    Ext (quotientModule k) (quotientModule k) 2 ≃ₗ[k] k :=
  ext2EquivBase k

/-- Example 15.101.10 (2): every positive reduced `Ext²` group in the nodal counterexample
vanishes. -/
@[stacks 0EH2 "vanishing of the reduced Ext groups in the nodal counterexample"]
theorem stageExt2IsZero (n : ℕ+) :
    IsZero
      (ModuleCat.of (StageRing k n)
        (Ext (stageModule k (quotientModule k) n)
          (stageModule k (quotientModule k) n) 2)) := sorry

end IadicFiniteModuleSystem.Ext.Nodal
