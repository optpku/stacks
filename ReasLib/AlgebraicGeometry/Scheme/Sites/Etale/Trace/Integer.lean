/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer

-- Local declaration justification (metaprogramming implementation): Exposed constructors
-- require private proof laws to remain accessible under Lean module visibility checks.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale.FiniteSupport
open scoped BigOperators AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.WeightingTrace

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The coefficient object of the constant integer sheaf. -/
abbrev integerCoeff : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} ℤ)

/-- The sheafification unit of the constant integer presheaf at an étale object. -/
def constantIntegerToSheafify {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] (U : S.Etale) :
    integerCoeff ⟶ (constantIntegerSheaf S.smallEtaleTopology).obj.obj (op U) :=
  (toSheafify S.smallEtaleTopology
      ((Functor.const S.Etaleᵒᵖ).obj integerCoeff)).app (op U)

/-- The canonical geometric point over a scheme point, with source field the
algebraic closure of the residue field. -/
def residueGeometricPoint {S : Scheme.{u}} (x : S) : GeometricPoint S :=
  GeometricPoint.of (AlgebraicClosure (S.residueField x))
    (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField x)
          (AlgebraicClosure (S.residueField x)))) ≫
      S.fromSpecResidueField x)

/-- The comparison from the stalk of a constant integer presheaf to `integerCoeff`. -/
def constantPresheafFiberToCoeff (S : Scheme.{u})
    (Φ : GrothendieckTopology.Point.{u} S.smallEtaleTopology) :
    Φ.presheafFiber.obj ((Functor.const S.Etaleᵒᵖ).obj integerCoeff) ⟶
      integerCoeff :=
  Φ.presheafFiberDesc (fun _ _ ↦ 𝟙 integerCoeff)

/-- The geometric point of `S` obtained by composing a geometric point of an
étale `S`-scheme with its structure morphism. -/
def etaleGeometricPoint {S : Scheme.{u}} (U : S.Etale)
    (ū : GeometricPoint U.left) : GeometricPoint S where
  toFieldValuedPoint := FieldValuedPoint.of ū.K (ū.hom ≫ U.hom)
  isAlgClosed := ū.isAlgClosed

/-- Evaluating a section of `underline ℤ` at a geometric point of `U`, via the
geometric germ and the stalk comparison of sheafification. -/
def integerGermValue {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    (U : S.Etale) (σ : (constantIntegerSheaf S.smallEtaleTopology).obj.obj (op U))
    (ū : GeometricPoint U.left) : ℤ :=
  (((constantPresheafFiberToCoeff S
        (toSmallEtalePoint (etaleGeometricPoint U ū))).hom
      ((((toSmallEtalePoint (etaleGeometricPoint U ū)).presheafToSheafCompSheafFiberIso
            AddCommGrpCat.{u}).hom.app
          ((Functor.const S.Etaleᵒᵖ).obj integerCoeff)).hom
        (((toSmallEtalePoint (etaleGeometricPoint U ū)).toPresheafFiber U
            (Over.homMk ū.hom) (constantIntegerSheaf S.smallEtaleTopology).obj).hom σ)))).down

/-- Evaluating a section of `underline ℤ` at a point, via the residue-field
geometric point. -/
def integerSectionValue {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    (U : S.Etale) (σ : (constantIntegerSheaf S.smallEtaleTopology).obj.obj (op U))
    (x : U.left) : ℤ :=
  integerGermValue U σ (residueGeometricPoint x)

/-- The clopen level set of a locally constant integer-valued function on an
étale `Y`-scheme. -/
def locallyConstantLevelOpen (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) : V.left.Opens :=
  ⟨{v | φ v = n}, hφ.isOpen_fiber n⟩

/-- The étale `Y`-scheme associated to a level set of a locally constant
function on `V`. -/
def locallyConstantLevelEtale (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) : Y.Etale :=
  mk ((locallyConstantLevelOpen V φ hφ n).ι ≫ V.hom)

/-- The open immersion of a level set as a morphism of étale `Y`-schemes. -/
def locallyConstantLevelHom (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    locallyConstantLevelEtale V φ hφ n ⟶ V :=
  MorphismProperty.Over.homMk (locallyConstantLevelOpen V φ hφ n).ι sorry

/-- The family of level-set morphisms covers `V` in the small étale topology. -/
private theorem locallyConstantLevel_covers (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) :
    Sieve.ofArrows _ (locallyConstantLevelHom V φ hφ) ∈ Y.smallEtaleTopology V :=
  sorry

/-- Constant integer sections on the level sets of `φ`, as a compatible family
out of `integerCoeff`. -/
def locallyConstantLevelFamily (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    integerCoeff ⟶
      (constantIntegerSheaf Y.smallEtaleTopology).obj.obj
        (op (locallyConstantLevelEtale V φ hφ n)) :=
  (n • 𝟙 integerCoeff) ≫
    constantIntegerToSheafify (locallyConstantLevelEtale V φ hφ n)

/-- Compatibility of the constant integer family on overlapping level sets. -/
private theorem locallyConstantLevelFamily_compatible (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) ⦃W : Y.Etale⦄ ⦃i j : ℤ⦄
    (a : W ⟶ locallyConstantLevelEtale V φ hφ i)
    (b : W ⟶ locallyConstantLevelEtale V φ hφ j)
    (hab : a ≫ locallyConstantLevelHom V φ hφ i =
      b ≫ locallyConstantLevelHom V φ hφ j) :
    locallyConstantLevelFamily V φ hφ i ≫
        (constantIntegerSheaf Y.smallEtaleTopology).obj.map a.op =
      locallyConstantLevelFamily V φ hφ j ≫
        (constantIntegerSheaf Y.smallEtaleTopology).obj.map b.op :=
  sorry

/-- The section of `underline ℤ` on `V` associated to a locally constant
integer-valued function, obtained by amalgamating constant sections on the
clopen level sets. -/
def locallyConstantIntegerSection (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) :
    (constantIntegerSheaf Y.smallEtaleTopology).obj.obj (op V) :=
  ((constantIntegerSheaf Y.smallEtaleTopology).property.amalgamateOfArrows
        (locallyConstantLevelHom V φ hφ) (locallyConstantLevel_covers V φ hφ)
        (locallyConstantLevelFamily V φ hφ) (locallyConstantLevelFamily_compatible V φ hφ)).hom
    (ULift.up (1 : ℤ))

/-- The open of `X_V` corresponding to an admissible support, transported along
`pullbackSymmetry` to the weighting convention `pullback f V.hom`. -/
def supportOpen {V : Y.Etale} (A : Admissible f V) :
    (pullback f V.hom).Opens :=
  (pullbackSymmetry V.hom f).hom ''ᵁ A.ambient

/-- Restriction of a weighting to the transported ambient open of an admissible
support. -/
def supportRestriction {V : Y.Etale} (A : Admissible f V)
    (w : X → ℤ) (u : supportOpen f A) : ℤ :=
  w (((supportOpen f A).ι ≫ pullback.fst f V.hom) u)

/-- The point of the ambient étale object corresponding to a transported
support point. -/
def supportAmbientPoint {V : Y.Etale} (A : Admissible f V)
    (u : supportOpen f A) :
    (mk (A.ambient.ι ≫ baseChangeToSource f V)).left :=
  ⟨(pullbackSymmetry V.hom f).inv ((supportOpen f A).ι u), sorry⟩

/-- Pointwise product of the integer values of a supported section of
`underline ℤ` with a weighting, on a transported admissible support. -/
def integerWeightedRestriction {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) (w : X → ℤ)
    (u : supportOpen f A) : ℤ :=
  integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
      (supportAmbientPoint f A u) *
    supportRestriction f A w u

/-- The nonzero support of the integer section in a single fibre. The ambient
open itself may have infinitely many points over the base point. -/
def integerFiberSupport {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) (y : V.left) :
    Set (supportOpen f A) :=
  {u | ((supportOpen f A).ι ≫ pullback.snd f V.hom) u = y ∧
    integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
      (supportAmbientPoint f A u) ≠ 0}

/-- A supported section vanishes outside the admissible closed subset, whose
map to `V` is finite. Thus its nonzero support in each fibre is finite. -/
theorem integerFiberSupport_finite {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) (y : V.left) :
    (integerFiberSupport f A σ y).Finite := sorry

/-- Sum a contribution over a section's finite nonzero fibre support. Neither
the ambient fibres nor the global range of the section need be finite. -/
def supportedFiberSum {ι κ : Type u} (p : ι → κ) (s a : ι → ℤ)
    (hf : ∀ y, {i | p i = y ∧ s i ≠ 0}.Finite) (y : κ) : ℤ :=
  (hf y).toFinset.sum a

/-- The separable-degree weighted contribution of an ambient point. -/
def integerFiberContribution {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) (w : X → ℤ)
    (u : supportOpen f A) : ℤ :=
  integerWeightedRestriction f A σ w u *
    (@Field.finSepDegree
      (V.left.residueField (((supportOpen f A).ι ≫ pullback.snd f V.hom) u))
      ((supportOpen f A).toScheme.residueField u) _ _
      (Scheme.Hom.residueFieldAlgebra
        ((supportOpen f A).ι ≫ pullback.snd f V.hom) u) : ℤ)

/-- Integral over the finite nonzero support in each fibre, not over the
possibly infinite fibre of the ambient open. -/
def integerFiberIntegral {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) (w : X → ℤ) :
    V.left → ℤ :=
  supportedFiberSum
    (fun u ↦ ((supportOpen f A).ι ≫ pullback.snd f V.hom) u)
    (fun u ↦ integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
      (supportAmbientPoint f A u))
    (integerFiberContribution f A σ w) (integerFiberSupport_finite f A σ)

/-- The integral uses exactly the nonzero support in the specified fibre. -/
theorem integerFiberIntegral_eq {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) (w : X → ℤ) (y : V.left) :
    integerFiberIntegral f A σ w y =
      (integerFiberSupport_finite f A σ y).toFinset.sum
        (integerFiberContribution f A σ w) := rfl

/-- The fibre integral of a supported integer section against a weighting is
locally constant. -/
theorem integerFiberIntegral_isLocallyConstant {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A)
    {w : X → ℤ} (hw : f.IsWeighting w) :
    IsLocallyConstant (integerFiberIntegral f A σ w) :=
  sorry

/-- Integrating the zero supported section gives the zero integer section. -/
private theorem integerSectionsHom_map_zero {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w) :
    locallyConstantIntegerSection V (integerFiberIntegral f A 0 w)
        (integerFiberIntegral_isLocallyConstant f A 0 hw) = 0 := sorry

/-- Integration of supported integer sections is additive. -/
private theorem integerSectionsHom_map_add {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w)
    (σ τ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) :
    locallyConstantIntegerSection V (integerFiberIntegral f A (σ + τ) w)
        (integerFiberIntegral_isLocallyConstant f A (σ + τ) hw) =
      locallyConstantIntegerSection V (integerFiberIntegral f A σ w)
        (integerFiberIntegral_isLocallyConstant f A σ hw) +
      locallyConstantIntegerSection V (integerFiberIntegral f A τ w)
        (integerFiberIntegral_isLocallyConstant f A τ hw) := sorry

/-- The map `H_Z(underline ℤ) ⟶ underline ℤ(V)` sending a supported section `s`
to the fibre-integral section of the product of the values of `s` with `w`,
recovering `∑_{n ≠ 0} n • ∫_{U_n → V} w|U_n`. -/
def integerSectionsHom {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w) :
    sections f (constantIntegerSheaf X.smallEtaleTopology) A ⟶
      (constantIntegerSheaf Y.smallEtaleTopology).obj.obj (op V) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        locallyConstantIntegerSection V (integerFiberIntegral f A σ w)
          (integerFiberIntegral_isLocallyConstant f A σ hw)
      map_zero' := integerSectionsHom_map_zero f A hw
      map_add' := integerSectionsHom_map_add f A hw }

/-- Evaluating the integer support map returns the fibre-integral section of
the product of the section values with `w`. -/
theorem integerSectionsHom_apply {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w)
    (σ : sections f (constantIntegerSheaf X.smallEtaleTopology) A) :
    (integerSectionsHom f A hw).hom σ =
      locallyConstantIntegerSection V (integerFiberIntegral f A σ w)
        (integerFiberIntegral_isLocallyConstant f A σ hw) :=
  sorry

/-- Cocone of fibre-integral maps out of the finite-support diagram of
`underline ℤ` on `X_V`. -/
def integerCocone (V : Y.Etale) {w : X → ℤ} (hw : f.IsWeighting w) :
    Cocone (diagram f (constantIntegerSheaf X.smallEtaleTopology) V) :=
  Cocone.mk ((constantIntegerSheaf Y.smallEtaleTopology).obj.obj (op V))
    { app := fun A ↦ integerSectionsHom f A hw
      naturality := sorry }

/-- The component at `V` of the integer trace on `f_{p!} underline ℤ`. -/
def integerTraceApp (V : Y.Etale) {w : X → ℤ}
    (hw : f.IsWeighting w) :
    ((lowerShriekPresheaf f).obj (constantIntegerSheaf X.smallEtaleTopology)).obj (op V) ⟶
      (constantIntegerSheaf Y.smallEtaleTopology).obj.obj (op V) :=
  colimit.desc (diagram f (constantIntegerSheaf X.smallEtaleTopology) V)
    (integerCocone f V hw)

/-- The presheaf-level integer trace `f_{p!} underline ℤ ⟶ underline ℤ`. -/
def integerTracePresheaf {w : X → ℤ} (hw : f.IsWeighting w) :
    (lowerShriekPresheaf f).obj (constantIntegerSheaf X.smallEtaleTopology) ⟶
      (constantIntegerSheaf Y.smallEtaleTopology).obj where
  app V := integerTraceApp f V.unop hw
  naturality := sorry

/-- Evaluating the integer presheaf trace at `V` is `integerTraceApp`. -/
theorem integerTracePresheaf_app (V : Y.Etale) {w : X → ℤ}
    (hw : f.IsWeighting w) :
    (integerTracePresheaf f hw).app (op V) =
      integerTraceApp f V hw :=
  sorry

/-- The sheaf-level integer trace `Tr_{f, w, underline ℤ} : f_! underline ℤ ⟶ underline ℤ`. -/
def integerTrace {w : X → ℤ} (hw : f.IsWeighting w) :
    (lowerShriek f).obj (constantIntegerSheaf X.smallEtaleTopology) ⟶
      constantIntegerSheaf Y.smallEtaleTopology :=
  ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
      ((lowerShriekPresheaf f).obj (constantIntegerSheaf X.smallEtaleTopology))
      (constantIntegerSheaf Y.smallEtaleTopology)).symm
    (integerTracePresheaf f hw)

end AlgebraicGeometry.Scheme.Etale.WeightingTrace

end
