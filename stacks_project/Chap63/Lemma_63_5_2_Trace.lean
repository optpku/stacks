module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
public import stacks_project.Chap63.Lemma_63_4_2_StalkCoproduct
public import stacks_project.Chap63.Lemma_63_4_5
public import stacks_project.Chap63.Lemma_63_5_1
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»

/-!
# Weighting traces for locally quasi-finite morphisms

The morphism `Tr_{f, w, F} : f_! f⁻¹ F ⟶ F` of abelian étale sheaves. On
`underline ℤ` the components send a compactly supported section `s` to
`∑_{n ≠ 0} n • locallyConstantIntegerSection (∫_{U_n → V} w|U_n)`; the general
map is the image of `Tr_ℤ ⊗ 𝟙` under the projection identification
`f_! f⁻¹ F ≅ f_! underline ℤ ⊗ F` after transporting along
`forget₂ (ModuleCat (ULift ℤ)) AddCommGrpCat`.
-/

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

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The constant sheaf of integers on the small étale site of a scheme. -/
abbrev etaleConstantIntegerSheaf (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} :=
  constantIntegerSheaf S.smallEtaleTopology

/-- Unfolding `etaleConstantIntegerSheaf` recovers `constantIntegerSheaf`. -/
theorem etaleConstantIntegerSheaf_eq (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] :
    etaleConstantIntegerSheaf S = constantIntegerSheaf S.smallEtaleTopology :=
  sorry

/-- The coefficient object of the constant integer sheaf. -/
abbrev integerCoeff : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} ℤ)

/-- The sheafification unit of the constant integer presheaf at an étale object. -/
def constantIntegerToSheafify {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] (U : S.Etale) :
    integerCoeff ⟶ (etaleConstantIntegerSheaf S).obj.obj (op U) :=
  (toSheafify S.smallEtaleTopology
      ((Functor.const S.Etaleᵒᵖ).obj integerCoeff)).app (op U)

/-- The sheafification unit at `U` is `toSheafify` of the constant integer
presheaf. -/
theorem constantIntegerToSheafify_eq {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] (U : S.Etale) :
    constantIntegerToSheafify U =
      (toSheafify S.smallEtaleTopology
          ((Functor.const S.Etaleᵒᵖ).obj integerCoeff)).app (op U) :=
  sorry

/-- The canonical geometric point over a scheme point, with source field the
algebraic closure of the residue field. -/
def residueGeometricPoint {S : Scheme.{u}} (x : S) : GeometricPoint S :=
  GeometricPoint.of (AlgebraicClosure (S.residueField x))
    (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField x)
          (AlgebraicClosure (S.residueField x)))) ≫
      S.fromSpecResidueField x)

/-- The image of `residueGeometricPoint x` is `x`. -/
theorem residueGeometricPoint_image {S : Scheme.{u}} (x : S) :
    (residueGeometricPoint x).image = x :=
  sorry

/-- The comparison from the stalk of a constant integer presheaf to `integerCoeff`. -/
def constantPresheafFiberToCoeff (S : Scheme.{u})
    (Φ : GrothendieckTopology.Point.{u} S.smallEtaleTopology) :
    Φ.presheafFiber.obj ((Functor.const S.Etaleᵒᵖ).obj integerCoeff) ⟶
      integerCoeff :=
  Φ.presheafFiberDesc (fun _ _ ↦ 𝟙 integerCoeff)

/-- The geometric point of `S` obtained by composing a geometric point of an
étale `S`-scheme with its structure morphism. -/
def etaleGeometricPoint {S : Scheme.{u}} (U : S.Etale)
    (ū : GeometricPoint U.left) : GeometricPoint S :=
  GeometricPoint.of ū.K (ū.hom ≫ U.hom)

/-- The structure morphism of `etaleGeometricPoint` is `ū.hom ≫ U.hom`. -/
theorem etaleGeometricPoint_hom {S : Scheme.{u}} (U : S.Etale)
    (ū : GeometricPoint U.left) :
    (etaleGeometricPoint U ū).hom = ū.hom ≫ U.hom :=
  sorry

/-- Evaluating a section of `underline ℤ` at a geometric point of `U`, via the
geometric germ and the stalk comparison of sheafification. -/
def integerGermValue {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    (U : S.Etale) (σ : (etaleConstantIntegerSheaf S).obj.obj (op U))
    (ū : GeometricPoint U.left) : ℤ :=
  (((constantPresheafFiberToCoeff S
        (toSmallEtalePoint (etaleGeometricPoint U ū))).hom
      ((((toSmallEtalePoint (etaleGeometricPoint U ū)).presheafToSheafCompSheafFiberIso
            AddCommGrpCat.{u}).hom.app
          ((Functor.const S.Etaleᵒᵖ).obj integerCoeff)).hom
        (((toSmallEtalePoint (etaleGeometricPoint U ū)).toPresheafFiber U
            (Over.homMk ū.hom) (etaleConstantIntegerSheaf S).obj).hom σ)))).down

/-- `integerGermValue` is the transported geometric germ in `ℤ`. -/
theorem integerGermValue_eq {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    (U : S.Etale) (σ : (etaleConstantIntegerSheaf S).obj.obj (op U))
    (ū : GeometricPoint U.left) :
    integerGermValue U σ ū =
      (((constantPresheafFiberToCoeff S
            (toSmallEtalePoint (etaleGeometricPoint U ū))).hom
          ((((toSmallEtalePoint (etaleGeometricPoint U ū)).presheafToSheafCompSheafFiberIso
                AddCommGrpCat.{u}).hom.app
              ((Functor.const S.Etaleᵒᵖ).obj integerCoeff)).hom
            (((toSmallEtalePoint (etaleGeometricPoint U ū)).toPresheafFiber U
                (Over.homMk ū.hom)
                (etaleConstantIntegerSheaf S).obj).hom σ)))).down :=
  sorry

/-- Evaluating a section of `underline ℤ` at a point, via the residue-field
geometric point. -/
def integerSectionValue {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    (U : S.Etale) (σ : (etaleConstantIntegerSheaf S).obj.obj (op U))
    (x : U.left) : ℤ :=
  integerGermValue U σ (residueGeometricPoint x)

/-- Unfolding `integerSectionValue` recovers evaluation at
`residueGeometricPoint`. -/
theorem integerSectionValue_eq {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    (U : S.Etale) (σ : (etaleConstantIntegerSheaf S).obj.obj (op U))
    (x : U.left) :
    integerSectionValue U σ x =
      integerGermValue U σ (residueGeometricPoint x) :=
  sorry

/-- The clopen level set of a locally constant integer-valued function on an
étale `Y`-scheme. -/
def locallyConstantLevelOpen (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) : V.left.Opens :=
  ⟨{v | φ v = n}, hφ.isOpen_fiber n⟩

/-- The underlying set of `locallyConstantLevelOpen` is the fibre of `φ`. -/
theorem mem_locallyConstantLevelOpen (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) (v : V.left) :
    v ∈ locallyConstantLevelOpen V φ hφ n ↔ φ v = n :=
  sorry

/-- The étale `Y`-scheme associated to a level set of a locally constant
function on `V`. -/
def locallyConstantLevelEtale (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) : Y.Etale :=
  mk ((locallyConstantLevelOpen V φ hφ n).ι ≫ V.hom)

/-- The structure morphism of a level-set object is the open immersion of the
level set followed by `V.hom`. -/
theorem locallyConstantLevelEtale_hom (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    (locallyConstantLevelEtale V φ hφ n).hom =
      (locallyConstantLevelOpen V φ hφ n).ι ≫ V.hom :=
  sorry

/-- The open immersion of a level set as a morphism of étale `Y`-schemes. -/
def locallyConstantLevelHom (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    locallyConstantLevelEtale V φ hφ n ⟶ V :=
  MorphismProperty.Over.homMk (locallyConstantLevelOpen V φ hφ n).ι sorry

/-- The underlying scheme morphism of `locallyConstantLevelHom` is the open
immersion of the level set. -/
theorem locallyConstantLevelHom_left (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    (locallyConstantLevelHom V φ hφ n).left =
      (locallyConstantLevelOpen V φ hφ n).ι :=
  sorry

/-- The family of level-set morphisms covers `V` in the small étale topology. -/
theorem locallyConstantLevel_covers (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) :
    Sieve.ofArrows _ (locallyConstantLevelHom V φ hφ) ∈ Y.smallEtaleTopology V :=
  sorry

/-- Constant integer sections on the level sets of `φ`, as a compatible family
out of `integerCoeff`. -/
def locallyConstantLevelFamily (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    integerCoeff ⟶
      (etaleConstantIntegerSheaf Y).obj.obj
        (op (locallyConstantLevelEtale V φ hφ n)) :=
  (n • 𝟙 integerCoeff) ≫
    constantIntegerToSheafify (locallyConstantLevelEtale V φ hφ n)

/-- The level-set family at `n` is multiplication by `n` followed by the
sheafification unit. -/
theorem locallyConstantLevelFamily_eq (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) (n : ℤ) :
    locallyConstantLevelFamily V φ hφ n =
      (n • 𝟙 integerCoeff) ≫
        constantIntegerToSheafify (locallyConstantLevelEtale V φ hφ n) :=
  sorry

/-- Compatibility of the constant integer family on overlapping level sets. -/
theorem locallyConstantLevelFamily_compatible (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) ⦃W : Y.Etale⦄ ⦃i j : ℤ⦄
    (a : W ⟶ locallyConstantLevelEtale V φ hφ i)
    (b : W ⟶ locallyConstantLevelEtale V φ hφ j)
    (hab : a ≫ locallyConstantLevelHom V φ hφ i =
      b ≫ locallyConstantLevelHom V φ hφ j) :
    locallyConstantLevelFamily V φ hφ i ≫
        (etaleConstantIntegerSheaf Y).obj.map a.op =
      locallyConstantLevelFamily V φ hφ j ≫
        (etaleConstantIntegerSheaf Y).obj.map b.op :=
  sorry

/-- The section of `underline ℤ` on `V` associated to a locally constant
integer-valued function, obtained by amalgamating constant sections on the
clopen level sets. -/
def locallyConstantIntegerSection (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) :
    (etaleConstantIntegerSheaf Y).obj.obj (op V) :=
  ((etaleConstantIntegerSheaf Y).property.amalgamateOfArrows
        (locallyConstantLevelHom V φ hφ)
        (locallyConstantLevel_covers V φ hφ)
        (locallyConstantLevelFamily V φ hφ)
        (locallyConstantLevelFamily_compatible V φ hφ)).hom
    (ULift.up (1 : ℤ))

/-- The amalgamated section is the sheaf gluing of the constant values of `φ`. -/
theorem locallyConstantIntegerSection_spec (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ) :
    locallyConstantIntegerSection V φ hφ =
      ((etaleConstantIntegerSheaf Y).property.amalgamateOfArrows
          (locallyConstantLevelHom V φ hφ)
          (locallyConstantLevel_covers V φ hφ)
          (locallyConstantLevelFamily V φ hφ)
          (locallyConstantLevelFamily_compatible V φ hφ)).hom
        (ULift.up (1 : ℤ)) :=
  sorry

/-- The open of `X_V` corresponding to an admissible support, transported along
`pullbackSymmetry` to the weighting convention `pullback f V.hom`. -/
def weightingSupportOpen {V : Y.Etale} (A : Admissible f V) :
    (pullback f V.hom).Opens :=
  (pullbackSymmetry V.hom f).hom ''ᵁ A.ambient

/-- The transported support open is the image of the ambient open along
`pullbackSymmetry`. -/
theorem weightingSupportOpen_eq {V : Y.Etale} (A : Admissible f V) :
    weightingSupportOpen f A = (pullbackSymmetry V.hom f).hom ''ᵁ A.ambient :=
  sorry

/-- Restriction of a weighting to the transported ambient open of an admissible
support. -/
def weightingSupportRestriction {V : Y.Etale} (A : Admissible f V)
    (w : X → ℤ) (u : weightingSupportOpen f A) : ℤ :=
  w (((weightingSupportOpen f A).ι ≫ pullback.fst f V.hom) u)

/-- The restricted weighting is `w` evaluated on the image in `X`. -/
theorem weightingSupportRestriction_eq {V : Y.Etale} (A : Admissible f V)
    (w : X → ℤ) (u : weightingSupportOpen f A) :
    weightingSupportRestriction f A w u =
      w (((weightingSupportOpen f A).ι ≫ pullback.fst f V.hom) u) :=
  sorry

/-- The point of the ambient étale object corresponding to a transported
support point. -/
def weightingSupportAmbientPoint {V : Y.Etale} (A : Admissible f V)
    (u : weightingSupportOpen f A) :
    (mk (A.ambient.ι ≫ baseChangeToSource f V)).left :=
  ⟨(pullbackSymmetry V.hom f).inv ((weightingSupportOpen f A).ι u), sorry⟩

/-- The ambient point is the inverse image of the transported support point
along `pullbackSymmetry`. -/
theorem weightingSupportAmbientPoint_eq {V : Y.Etale} (A : Admissible f V)
    (u : weightingSupportOpen f A) :
    (weightingSupportAmbientPoint f A u).1 =
      (pullbackSymmetry V.hom f).inv ((weightingSupportOpen f A).ι u) :=
  sorry

/-- Pointwise product of the integer values of a supported section of
`underline ℤ` with a weighting, on a transported admissible support. -/
def weightingIntegerWeightedRestriction {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ)
    (u : weightingSupportOpen f A) : ℤ :=
  integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
      (weightingSupportAmbientPoint f A u) *
    weightingSupportRestriction f A w u

/-- The weighted restriction is the product of the section value with `w`. -/
theorem weightingIntegerWeightedRestriction_eq {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (etaleConstantIntegerSheaf X) A)
    (w : X → ℤ) (u : weightingSupportOpen f A) :
    weightingIntegerWeightedRestriction f A σ w u =
      integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
          (weightingSupportAmbientPoint f A u) *
        weightingSupportRestriction f A w u :=
  sorry

/-- The nonzero support of the integer section in a single fibre. The ambient
open itself may have infinitely many points over the base point. -/
def weightingIntegerFiberSupport {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (y : V.left) :
    Set (weightingSupportOpen f A) :=
  {u | ((weightingSupportOpen f A).ι ≫ pullback.snd f V.hom) u = y ∧
    integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
      (weightingSupportAmbientPoint f A u) ≠ 0}

/-- A supported section vanishes outside the admissible closed subset, whose
map to `V` is finite. Thus its nonzero support in each fibre is finite. -/
theorem weightingIntegerFiberSupport_finite {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (y : V.left) :
    (weightingIntegerFiberSupport f A σ y).Finite := sorry

/-- Sum a contribution over a section's finite nonzero fibre support. Neither
the ambient fibres nor the global range of the section need be finite. -/
def weightingSupportedFiberSum {ι κ : Type u} (p : ι → κ) (s a : ι → ℤ)
    (hf : ∀ y, {i | p i = y ∧ s i ≠ 0}.Finite) (y : κ) : ℤ :=
  (hf y).toFinset.sum a

/-- The separable-degree weighted contribution of an ambient point. -/
def weightingIntegerFiberContribution {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ)
    (u : weightingSupportOpen f A) : ℤ :=
  weightingIntegerWeightedRestriction f A σ w u *
    (@Field.finSepDegree
      (V.left.residueField (((weightingSupportOpen f A).ι ≫ pullback.snd f V.hom) u))
      ((weightingSupportOpen f A).toScheme.residueField u) _ _
      (Scheme.Hom.residueFieldAlgebra
        ((weightingSupportOpen f A).ι ≫ pullback.snd f V.hom) u) : ℤ)

/-- Integral over the finite nonzero support in each fibre, not over the
possibly infinite fibre of the ambient open. -/
def weightingIntegerFiberIntegral {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ) :
    V.left → ℤ :=
  weightingSupportedFiberSum
    (fun u ↦ ((weightingSupportOpen f A).ι ≫ pullback.snd f V.hom) u)
    (fun u ↦ integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
      (weightingSupportAmbientPoint f A u))
    (weightingIntegerFiberContribution f A σ w)
    (weightingIntegerFiberSupport_finite f A σ)

/-- The integral uses exactly the nonzero support in the specified fibre. -/
theorem weightingIntegerFiberIntegral_eq {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ) (y : V.left) :
    weightingIntegerFiberIntegral f A σ w y =
      (weightingIntegerFiberSupport_finite f A σ y).toFinset.sum
        (weightingIntegerFiberContribution f A σ w) := rfl

/-- The fibre integral of a supported integer section against a weighting is
locally constant. -/
theorem weightingIntegerFiberIntegral_isLocallyConstant {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (etaleConstantIntegerSheaf X) A)
    {w : X → ℤ} (hw : f.IsWeighting w) :
    IsLocallyConstant (weightingIntegerFiberIntegral f A σ w) :=
  sorry

/-- The map `H_Z(underline ℤ) ⟶ underline ℤ(V)` sending a supported section `s`
to the fibre-integral section of the product of the values of `s` with `w`,
recovering `∑_{n ≠ 0} n • ∫_{U_n → V} w|U_n`. -/
def weightingIntegerSectionsHom {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w) :
    sections f (etaleConstantIntegerSheaf X) A ⟶
      (etaleConstantIntegerSheaf Y).obj.obj (op V) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        locallyConstantIntegerSection V (weightingIntegerFiberIntegral f A σ w)
          (weightingIntegerFiberIntegral_isLocallyConstant f A σ hw)
      map_zero' := sorry
      map_add' := sorry }

/-- Evaluating the integer support map returns the fibre-integral section of
the product of the section values with `w`. -/
theorem weightingIntegerSectionsHom_apply {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w)
    (σ : sections f (etaleConstantIntegerSheaf X) A) :
    (weightingIntegerSectionsHom f A hw).hom σ =
      locallyConstantIntegerSection V (weightingIntegerFiberIntegral f A σ w)
        (weightingIntegerFiberIntegral_isLocallyConstant f A σ hw) :=
  sorry


/-- Around each base point only finitely many nonzero values of the supported
section occur. This is local on `V`, with no global quasi-compactness assumption. -/
theorem weightingIntegerSupportValues_locallyFinite {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (etaleConstantIntegerSheaf X) A)
    (y : V.left) :
    ∃ U : V.left.Opens, y ∈ U ∧ ∃ N : Finset ℤ,
      ∀ u : weightingSupportOpen f A,
        ((weightingSupportOpen f A).ι ≫ pullback.snd f V.hom) u ∈ U →
        integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
          (weightingSupportAmbientPoint f A u) ≠ 0 →
        integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
          (weightingSupportAmbientPoint f A u) ∈ N := sorry

/-- Open of `X_V` on which a compactly supported integer section takes the
value `n`, as a locally closed open of the weighting pullback. -/
def weightingIntegerLevelOpen {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (n : ℤ) :
    (pullback f V.hom).Opens :=
  ⟨{x : (pullback f V.hom : Scheme.{u}) |
      ∃ hx : x ∈ weightingSupportOpen f A,
        integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
          (weightingSupportAmbientPoint f A ⟨x, hx⟩) = n}, sorry⟩

/-- Membership in `weightingIntegerLevelOpen` is evaluation of the supported
section on the transported support. -/
theorem mem_weightingIntegerLevelOpen {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (n : ℤ)
    (x : (pullback f V.hom : Scheme.{u})) :
    x ∈ weightingIntegerLevelOpen f A σ n ↔
      ∃ hx : x ∈ weightingSupportOpen f A,
        integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
            (weightingSupportAmbientPoint f A ⟨x, hx⟩) = n :=
  sorry

/-- The structure morphism of a nonzero level set of a compactly supported
integer section has finite fibres. -/
theorem weightingIntegerLevelOpen_isFinite {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (etaleConstantIntegerSheaf X) A)
    {n : ℤ} (hn : n ≠ 0) :
    IsFinite ((weightingIntegerLevelOpen f A σ n).ι ≫ pullback.snd f V.hom) := sorry

/-- The nonzero level is finite over the base because it is closed in the
admissible finite support, so its point fibres are finite. -/
theorem weightingIntegerLevelOpen_tendstoCofinite {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (etaleConstantIntegerSheaf X) A)
    {n : ℤ} (hn : n ≠ 0) :
    Filter.TendstoCofinite fun u : weightingIntegerLevelOpen f A σ n ↦
      ((weightingIntegerLevelOpen f A σ n).ι ≫ pullback.snd f V.hom) u :=
  sorry

/-- Restriction of a weighting to a nonzero level set of a compactly supported
integer section. -/
def weightingIntegerLevelRestriction {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ) (n : ℤ) :
    weightingIntegerLevelOpen f A σ n → ℤ :=
  fun u ↦ w (((weightingIntegerLevelOpen f A σ n).ι ≫ pullback.fst f V.hom) u)

/-- The level-set restriction of a weighting is evaluation of `w` on the
image in `X`. -/
theorem weightingIntegerLevelRestriction_eq {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ) (n : ℤ)
    (u : weightingIntegerLevelOpen f A σ n) :
    weightingIntegerLevelRestriction f A σ w n u =
      w (((weightingIntegerLevelOpen f A σ n).ι ≫ pullback.fst f V.hom) u) :=
  sorry

/-- Fibre integral of a weighting on the level set where a compactly supported
integer section takes the value `n`. -/
def weightingIntegerLevelFiberIntegral {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ) {n : ℤ}
    (hn : n ≠ 0) : V.left → ℤ :=
  ((weightingIntegerLevelOpen f A σ n).ι ≫ pullback.snd f V.hom).fiberIntegral
    (weightingIntegerLevelOpen_tendstoCofinite f A σ hn)
    (weightingIntegerLevelRestriction f A σ w n)

/-- The level-set fibre integral is the finite-morphism fibre integral of the
restricted weighting. -/
theorem weightingIntegerLevelFiberIntegral_eq {V : Y.Etale} (A : Admissible f V)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (w : X → ℤ) {n : ℤ}
    (hn : n ≠ 0) :
    weightingIntegerLevelFiberIntegral f A σ w hn =
      ((weightingIntegerLevelOpen f A σ n).ι ≫
          pullback.snd f V.hom).fiberIntegral
        (weightingIntegerLevelOpen_tendstoCofinite f A σ hn)
        (weightingIntegerLevelRestriction f A σ w n) :=
  sorry

/-- A weighting has locally constant fibre integral on every nonzero level set
of a compactly supported integer section. -/
theorem weightingIntegerLevelFiberIntegral_isLocallyConstant {V : Y.Etale}
    (A : Admissible f V) (σ : sections f (etaleConstantIntegerSheaf X) A)
    {w : X → ℤ} (hw : f.IsWeighting w) {n : ℤ} (hn : n ≠ 0) :
    IsLocallyConstant (weightingIntegerLevelFiberIntegral f A σ w hn) :=
  sorry

/-- The summand `n • ∫_{U_n → V} w|U_n` of the source integer trace formula,
or zero when `n = 0`. -/
def weightingIntegerLevelSummand {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (n : ℤ) :
    (etaleConstantIntegerSheaf Y).obj.obj (op V) :=
  if hn : n ≠ 0 then
    n • locallyConstantIntegerSection V
      (weightingIntegerLevelFiberIntegral f A σ w hn)
      (weightingIntegerLevelFiberIntegral_isLocallyConstant f A σ hw hn)
  else
    0

/-- On a nonzero level the summand is `n` times the fibre-integral section of
`w` on `U_n`. -/
theorem weightingIntegerLevelSummand_of_ne {V : Y.Etale} (A : Admissible f V)
    {w : X → ℤ} (hw : f.IsWeighting w)
    (σ : sections f (etaleConstantIntegerSheaf X) A) {n : ℤ} (hn : n ≠ 0) :
    weightingIntegerLevelSummand f A hw σ n =
      n • locallyConstantIntegerSection V
        (weightingIntegerLevelFiberIntegral f A σ w hn)
        (weightingIntegerLevelFiberIntegral_isLocallyConstant f A σ hw hn) :=
  sorry

/-- On a base open where the nonzero values belong to a finite set, the trace
is the source's finite level sum. Such opens cover `V` by local finiteness. -/
theorem weightingIntegerSectionsHom_eq_levelSum {V : Y.Etale}
    (A : Admissible f V) {w : X → ℤ} (hw : f.IsWeighting w)
    (σ : sections f (etaleConstantIntegerSheaf X) A) (U : V.left.Opens)
    (N : Finset ℤ)
    (hN : ∀ u : weightingSupportOpen f A,
      ((weightingSupportOpen f A).ι ≫ pullback.snd f V.hom) u ∈ U →
      integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
        (weightingSupportAmbientPoint f A u) ≠ 0 →
      integerSectionValue (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ.1
        (weightingSupportAmbientPoint f A u) ∈ N) :
    ((etaleConstantIntegerSheaf Y).obj.map
      (MorphismProperty.Over.homMk U.ι rfl : mk (U.ι ≫ V.hom) ⟶ V).op).hom
        ((weightingIntegerSectionsHom f A hw).hom σ) =
      ∑ n ∈ N.erase 0,
        ((etaleConstantIntegerSheaf Y).obj.map
          (MorphismProperty.Over.homMk U.ι rfl : mk (U.ι ≫ V.hom) ⟶ V).op).hom
            (weightingIntegerLevelSummand f A hw σ n) := sorry

/-- Cocone of fibre-integral maps out of the finite-support diagram of
`underline ℤ` on `X_V`. -/
def weightingIntegerCocone (V : Y.Etale) {w : X → ℤ} (hw : f.IsWeighting w) :
    Cocone (diagram f (etaleConstantIntegerSheaf X) V) :=
  Cocone.mk ((etaleConstantIntegerSheaf Y).obj.obj (op V))
    { app := fun A ↦ weightingIntegerSectionsHom f A hw
      naturality := sorry }

/-- The vertex of the integer fibre-integral cocone is `underline ℤ(V)`. -/
theorem weightingIntegerCocone_pt (V : Y.Etale) {w : X → ℤ}
    (hw : f.IsWeighting w) :
    (weightingIntegerCocone f V hw).pt =
      (etaleConstantIntegerSheaf Y).obj.obj (op V) :=
  sorry

/-- The component at `V` of the integer trace on `f_{p!} underline ℤ`. -/
def weightingTraceIntegerApp (V : Y.Etale) {w : X → ℤ}
    (hw : f.IsWeighting w) :
    ((lowerShriekPresheaf f).obj (etaleConstantIntegerSheaf X)).obj (op V) ⟶
      (etaleConstantIntegerSheaf Y).obj.obj (op V) :=
  colimit.desc (diagram f (etaleConstantIntegerSheaf X) V)
    (weightingIntegerCocone f V hw)

/-- The integer trace component is the colimit descent of fibre-integral
maps. -/
theorem weightingTraceIntegerApp_eq (V : Y.Etale) {w : X → ℤ}
    (hw : f.IsWeighting w) :
    weightingTraceIntegerApp f V hw =
      colimit.desc (diagram f (etaleConstantIntegerSheaf X) V)
        (weightingIntegerCocone f V hw) :=
  sorry

/-- The presheaf-level integer trace `f_{p!} underline ℤ ⟶ underline ℤ`. -/
def weightingTraceIntegerPresheaf {w : X → ℤ} (hw : f.IsWeighting w) :
    (lowerShriekPresheaf f).obj (etaleConstantIntegerSheaf X) ⟶
      (etaleConstantIntegerSheaf Y).obj where
  app V := weightingTraceIntegerApp f V.unop hw
  naturality := sorry

/-- Evaluating the integer presheaf trace at `V` is `weightingTraceIntegerApp`. -/
theorem weightingTraceIntegerPresheaf_app (V : Y.Etale) {w : X → ℤ}
    (hw : f.IsWeighting w) :
    (weightingTraceIntegerPresheaf f hw).app (op V) =
      weightingTraceIntegerApp f V hw :=
  sorry

/-- The sheaf-level integer trace `Tr_{f, w, underline ℤ} : f_! underline ℤ ⟶ underline ℤ`. -/
def weightingTraceInteger {w : X → ℤ} (hw : f.IsWeighting w) :
    (lowerShriek f).obj (etaleConstantIntegerSheaf X) ⟶
      etaleConstantIntegerSheaf Y :=
  ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
      ((lowerShriekPresheaf f).obj (etaleConstantIntegerSheaf X))
      (etaleConstantIntegerSheaf Y)).symm
    (weightingTraceIntegerPresheaf f hw)

/-- The integer trace is the sheafification adjunct of the fibre-integral
presheaf map. -/
theorem weightingTraceInteger_eq {w : X → ℤ} (hw : f.IsWeighting w) :
    weightingTraceInteger f hw =
      ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
          ((lowerShriekPresheaf f).obj (etaleConstantIntegerSheaf X))
          (etaleConstantIntegerSheaf Y)).symm
        (weightingTraceIntegerPresheaf f hw) :=
  sorry

/-- Comparison `f⁻¹ underline ℤ_Y ⟶ underline ℤ_X` from the constant sheaf
pullback unit. -/
def weightingConstantPullbackHom :
    (etaleAbelianSheafPullback f).obj (etaleConstantIntegerSheaf Y) ⟶
      etaleConstantIntegerSheaf X :=
  constantSheaf_sheafPullback_hom f integerCoeff

/-- The constant-sheaf comparison is `constantSheaf_sheafPullback_hom`. -/
theorem weightingConstantPullbackHom_eq :
    weightingConstantPullbackHom f =
      constantSheaf_sheafPullback_hom f integerCoeff :=
  sorry

/-- The geometric point of `Y` obtained by composing `x : Over f ȳ` with `f`. -/
def weightingImagePoint (ybar : GeometricPoint Y) (x : GeometricPoint.Over f ybar) :
    GeometricPoint Y where
  toFieldValuedPoint := FieldValuedPoint.of ybar.K (x.toScheme ≫ f)
  isAlgClosed := ybar.isAlgClosed

/-- The composite geometric point of an `Over f ȳ` point is `ȳ`, by `Over.fac`. -/
theorem weightingImagePoint_eq (ybar : GeometricPoint Y) (x : GeometricPoint.Over f ybar) :
    weightingImagePoint f ybar x = ybar :=
  congrArg (fun h : Spec (.of ybar.K) ⟶ Y ↦
      ({ toFieldValuedPoint := FieldValuedPoint.of ybar.K h
         isAlgClosed := ybar.isAlgClosed } : GeometricPoint Y))
    x.fac

/-- Small-étale pullback of a geometric point of `X` along `f` is initially
small. -/
instance weightingPullbackInitiallySmall (ybar : GeometricPoint Y)
    (x : GeometricPoint.Over f ybar) :
    InitiallySmall
      ((smallEtalePullback f ⋙
        (toSmallEtalePoint x.toGeometricPoint).fiber).Elements) :=
  sorry

/-- Fibre map sending a lift of `ȳ` over `V` to the pairing lift of `x̄` over
the base change of `V`. -/
def weightingImageToComapFiber (ybar : GeometricPoint Y) (x : GeometricPoint.Over f ybar) :
    (toSmallEtalePoint (weightingImagePoint f ybar x)).fiber ⟶
      smallEtalePullback f ⋙ (toSmallEtalePoint x.toGeometricPoint).fiber where
  app V :=
    TypeCat.ofHom fun φ ↦
      (Over.homMk (pullback.lift φ.left x.toScheme sorry) sorry :
        (smallEtalePullback f ⋙
          (toSmallEtalePoint x.toGeometricPoint).fiber).obj V)
  naturality := sorry

/-- Fibre map sending a pairing lift of `x̄` to its projection to `V`. -/
def weightingComapToImageFiber (ybar : GeometricPoint Y) (x : GeometricPoint.Over f ybar) :
    (smallEtalePullback f ⋙ (toSmallEtalePoint x.toGeometricPoint).fiber) ⟶
      (toSmallEtalePoint (weightingImagePoint f ybar x)).fiber where
  app V :=
    TypeCat.ofHom fun ψ ↦
      (Over.homMk (ψ.left ≫ pullback.fst V.hom f) sorry :
        (toSmallEtalePoint (weightingImagePoint f ybar x)).fiber.obj V)
  naturality := sorry

/-- Identification of the abelian sheaf fibre of `F` at `f(x̄)` with the fibre of
`f⁻¹ F` at `x̄`. -/
def weightingImagePullbackSheafFiberIso (ybar : GeometricPoint Y)
    (x : GeometricPoint.Over f ybar)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint (weightingImagePoint f ybar x)).sheafFiber.obj F ≅
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj
        ((etaleAbelianSheafPullback f).obj F) where
  hom :=
    (Hom.sheafFiber ⟨weightingImageToComapFiber f ybar x⟩).app F ≫
      ((toSmallEtalePoint x.toGeometricPoint).sheafFiberComapIsoOfMorphismOfSites
          (smallEtalePullback f) AddCommGrpCat.{u}).hom.app F
  inv :=
    ((toSmallEtalePoint x.toGeometricPoint).sheafFiberComapIsoOfMorphismOfSites
          (smallEtalePullback f) AddCommGrpCat.{u}).inv.app F ≫
      (Hom.sheafFiber ⟨weightingComapToImageFiber f ybar x⟩).app F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `weightingImagePullbackSheafFiberIso` is the image-to-comap
fibre map followed by the site-point comap comparison. -/
theorem weightingImagePullbackSheafFiberIso_hom (ybar : GeometricPoint Y)
    (x : GeometricPoint.Over f ybar)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingImagePullbackSheafFiberIso f ybar x F).hom =
      (Hom.sheafFiber ⟨weightingImageToComapFiber f ybar x⟩).app F ≫
        ((toSmallEtalePoint x.toGeometricPoint).sheafFiberComapIsoOfMorphismOfSites
            (smallEtalePullback f) AddCommGrpCat.{u}).hom.app F :=
  sorry

/-- Inverse-image identification of abelian étale stalks
`(f⁻¹ F)_x̄ ≅ F_ȳ` along `Over.fac`. -/
def weightingPullbackStalkIso (ybar : GeometricPoint Y) (x : GeometricPoint.Over f ybar)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj
        ((etaleAbelianSheafPullback f).obj F) ≅
      (toSmallEtalePoint ybar).sheafFiber.obj F :=
  (weightingImagePullbackSheafFiberIso f ybar x F).symm ≪≫
    eqToIso
      (congrArg (fun s : GeometricPoint Y ↦
          (toSmallEtalePoint s).sheafFiber.obj F)
        (weightingImagePoint_eq f ybar x))

/-- The forward map of `weightingPullbackStalkIso` is the inverse image-to-comap
comparison followed by transport along `Over.fac`. -/
theorem weightingPullbackStalkIso_hom (ybar : GeometricPoint Y)
    (x : GeometricPoint.Over f ybar)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingPullbackStalkIso f ybar x F).hom =
      (weightingImagePullbackSheafFiberIso f ybar x F).inv ≫
        (eqToIso
          (congrArg (fun s : GeometricPoint Y ↦
              (toSmallEtalePoint s).sheafFiber.obj F)
            (weightingImagePoint_eq f ybar x))).hom :=
  sorry

/-- Weighted sum of abelian stalks: the coproduct of copies of `F_ȳ` maps to
`F_ȳ` by `zsmul` with `w(x̄.image)` on the summand indexed by `x̄`. -/
def weightingStalkDesc (w : X → ℤ) (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (∐ fun _ : GeometricPoint.Over f ybar ↦ (toSmallEtalePoint ybar).sheafFiber.obj F) ⟶
      (toSmallEtalePoint ybar).sheafFiber.obj F :=
  Sigma.desc fun x : GeometricPoint.Over f ybar ↦
    w x.toGeometricPoint.image • 𝟙 ((toSmallEtalePoint ybar).sheafFiber.obj F)

/-- The weighted stalk descent is the coproduct of `zsmul` maps by
`w(x̄.image)`. -/
theorem weightingStalkDesc_eq (w : X → ℤ) (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingStalkDesc f w ybar F =
      Sigma.desc fun x : GeometricPoint.Over f ybar ↦
        w x.toGeometricPoint.image •
          𝟙 ((toSmallEtalePoint ybar).sheafFiber.obj F) :=
  sorry

/-- On the summand indexed by `x`, `weightingStalkDesc` is multiplication by
`w(x.image)`. -/
theorem weightingStalkDesc_app (w : X → ℤ) (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (x : GeometricPoint.Over f ybar) :
    Sigma.ι (fun _ : GeometricPoint.Over f ybar ↦
        (toSmallEtalePoint ybar).sheafFiber.obj F) x ≫
      weightingStalkDesc f w ybar F =
      w x.toGeometricPoint.image •
        𝟙 ((toSmallEtalePoint ybar).sheafFiber.obj F) :=
  sorry

/-- Coproduct of the pullback-stalk identifications
`(f⁻¹ F)_x̄ ≅ F_ȳ`. -/
def weightingPullbackStalkCoproductIso (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproduct f ybar).obj ((etaleAbelianSheafPullback f).obj F) ≅
      ∐ fun _ : GeometricPoint.Over f ybar ↦ (toSmallEtalePoint ybar).sheafFiber.obj F :=
  Sigma.mapIso fun x : GeometricPoint.Over f ybar ↦ weightingPullbackStalkIso f ybar x F

/-- The coproduct comparison is `Sigma.mapIso` of `weightingPullbackStalkIso`. -/
theorem weightingPullbackStalkCoproductIso_eq (ybar : GeometricPoint Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingPullbackStalkCoproductIso f ybar F =
      Sigma.mapIso fun x : GeometricPoint.Over f ybar ↦
        weightingPullbackStalkIso f ybar x F :=
  sorry

/-- The inverse-image of `F` along the small-étale pullback of `f`. -/
abbrev weightingPullback (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleAbelianSheafPullback f).obj F

/-- Unfolding `weightingPullback` recovers étale abelian sheaf pullback. -/
theorem weightingPullback_eq
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingPullback f F = (etaleAbelianSheafPullback f).obj F :=
  sorry

/-- Action of a locally constant integer function on a section of an abelian
étale sheaf, by amalgamating the scaled restrictions to the clopen level sets. -/
def locallyConstantZsmulSection (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (s : F.obj.obj (op V)) : F.obj.obj (op V) :=
  (F.property.amalgamateOfArrows
      (locallyConstantLevelHom V φ hφ)
      (locallyConstantLevel_covers V φ hφ)
      (fun n ↦ (n • 𝟙 (F.obj.obj (op V))) ≫
        F.obj.map (locallyConstantLevelHom V φ hφ n).op)
      sorry).hom s

/-- Scaling a section by a locally constant integer function is the amalgamation
of the restricted scaled sections. -/
theorem locallyConstantZsmulSection_spec (V : Y.Etale) (φ : V.left → ℤ)
    (hφ : IsLocallyConstant φ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (s : F.obj.obj (op V)) :
    locallyConstantZsmulSection V φ hφ F s =
      (F.property.amalgamateOfArrows
          (locallyConstantLevelHom V φ hφ)
          (locallyConstantLevel_covers V φ hφ)
          (fun n ↦ (n • 𝟙 (F.obj.obj (op V))) ≫
            F.obj.map (locallyConstantLevelHom V φ hφ n).op)
          sorry).hom s :=
  sorry

/-- Universe-lifted integers, used as the coefficient ring of the internal
`ℤ`-module transport. -/
abbrev weightingULiftInt : Type u := ULift.{u} ℤ

/-- Coefficient functor sending an abelian group to the associated
`ULift ℤ`-module. -/
def weightingAddCommGrpToModule :
    AddCommGrpCat.{u} ⥤ ModuleCat.{u} weightingULiftInt :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- Unfolding `weightingAddCommGrpToModule` recovers restriction of scalars
along `ULift.ringEquiv` after the inverse of `forget₂`. -/
theorem weightingAddCommGrpToModule_eq :
    weightingAddCommGrpToModule =
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv ⋙
        ModuleCat.restrictScalars
          (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom :=
  sorry

/-- Component of the coefficient counit at an abelian group. -/
def weightingAddCommGrpToModuleCounitApp (A : AddCommGrpCat.{u}) :
    (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u}).obj
      (weightingAddCommGrpToModule.obj A) ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦
        ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
            A).hom
          (x :
            (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
              ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv.obj A))
      map_zero' := sorry
      map_add' := sorry }

/-- Applying the coefficient counit recovers the counit of
`forget₂ (ModuleCat ℤ)`. -/
theorem weightingAddCommGrpToModuleCounitApp_apply (A : AddCommGrpCat.{u})
    (x :
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u}).obj
        (weightingAddCommGrpToModule.obj A)) :
    (weightingAddCommGrpToModuleCounitApp A).hom x =
      ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.counitIso.hom.app
          A).hom
        (x :
          (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
            ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv.obj A)) :=
  sorry

/-- Counit of the coefficient equivalence from abelian groups to
`ULift ℤ`-modules, as a natural transformation on underlying groups. -/
def weightingAddCommGrpToModuleCounit :
    weightingAddCommGrpToModule ⋙
        forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u} ⟶
      𝟭 AddCommGrpCat.{u} where
  app := weightingAddCommGrpToModuleCounitApp
  naturality := sorry

/-- The coefficient counit is an isomorphism. -/
instance weightingAddCommGrpToModuleCounit_isIso :
    IsIso weightingAddCommGrpToModuleCounit :=
  sorry

/-- The coefficient counit as an isomorphism of functors. -/
def weightingAddCommGrpToModuleCounitIso :
    weightingAddCommGrpToModule ⋙
        forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u} ≅
      𝟭 AddCommGrpCat.{u} :=
  asIso weightingAddCommGrpToModuleCounit

/-- Composition with `weightingAddCommGrpToModule` preserves étale sheaves. -/
public instance (priority := high) weightingAddCommGrpToModule_hasSheafCompose (S : Scheme.{u}) :
    S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule :=
  sorry

/-- Composition with `forget₂ (ModuleCat (ULift ℤ))` preserves étale sheaves. -/
public instance (priority := high) weightingForget₂_hasSheafCompose (S : Scheme.{u}) :
    S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u}) :=
  sorry

/-- Étale sites admit sheafification of `ULift ℤ`-modules. -/
public instance weightingModuleSheaf_hasSheafify (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt) :=
  sorry

/-- The sheafification class `W` is monoidal for étale sheaves of `ULift ℤ`-modules. -/
public instance weightingModuleSheaf_isMonoidal_W (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u} weightingULiftInt)).IsMonoidal :=
  sorry

/-- The monoidal structure on étale sheaves of `ULift ℤ`-modules, obtained by
sheafifying the pointwise module tensor. -/
public instance weightingModuleSheafMonoidalCategory (S : Scheme.{u}) :
    MonoidalCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)) :=
  Sheaf.monoidalCategory S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)

/-- Sheafification of étale `ULift ℤ`-module presheaves is monoidal. -/
public instance weightingPresheafToSheafMonoidal (S : Scheme.{u}) :
    (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)).Monoidal :=
  inferInstance

/-- `weightingAddCommGrpToModule` preserves étale sheafification. -/
public instance weightingAddCommGrpToModule_preservesSheafification (S : Scheme.{u}) :
    S.smallEtaleTopology.PreservesSheafification weightingAddCommGrpToModule :=
  sorry

/-- `forget₂ (ModuleCat (ULift ℤ))` preserves étale sheafification. -/
public instance weightingForget₂_preservesSheafification (S : Scheme.{u}) :
    S.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u}) :=
  sorry

/-- Left Kan extensions of module-valued presheaves along small-étale pullback. -/
public instance weightingPullback_hasLeftKanExtension_module
    (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} weightingULiftInt) :
    (smallEtalePullback f).op.HasLeftKanExtension P :=
  sorry

/-- Left Kan extensions of abelian presheaves along small-étale pullback. -/
public instance weightingPullback_hasLeftKanExtension_abelian
    (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtalePullback f).op.HasLeftKanExtension P :=
  sorry

/-- The coefficient functor preserves left Kan extensions along small-étale
pullback. -/
public instance weightingAddCommGrpToModule_preservesLeftKanExtensions :
    weightingAddCommGrpToModule.PreservesLeftKanExtensions
      (smallEtalePullback f).op :=
  sorry

/-- `forget₂ (ModuleCat (ULift ℤ))` preserves left Kan extensions along
small-étale pullback. -/
public instance weightingForget₂_preservesLeftKanExtensions :
    (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback f).op :=
  sorry

/-- Lift an abelian étale sheaf to a sheaf of `ULift ℤ`-modules. -/
def weightingAbelianToModule {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt) :=
  (sheafCompose S.smallEtaleTopology weightingAddCommGrpToModule).obj F

/-- Unfolding `weightingAbelianToModule` recovers `sheafCompose` of the
coefficient functor. -/
theorem weightingAbelianToModule_eq {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingAbelianToModule F =
      (sheafCompose S.smallEtaleTopology weightingAddCommGrpToModule).obj F :=
  sorry

/-- The constant integer sheaf, viewed as a sheaf of `ULift ℤ`-modules. -/
def weightingConstantIntegerModule (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule] :
    Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt) :=
  weightingAbelianToModule (etaleConstantIntegerSheaf S)

/-- Unfolding `weightingConstantIntegerModule` recovers the module lift of
`etaleConstantIntegerSheaf`. -/
theorem weightingConstantIntegerModule_eq (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule] :
    weightingConstantIntegerModule S =
      weightingAbelianToModule (etaleConstantIntegerSheaf S) :=
  sorry

/-- Forgetting `ULift ℤ`-module coefficients on sections, as a morphism of
abelian étale sheaves. -/
def weightingForgetAbelianHom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleModuleForget weightingULiftInt (weightingAbelianToModule F) ⟶ F :=
  ObjectProperty.homMk
    { app := fun U ↦ weightingAddCommGrpToModuleCounitApp (F.obj.obj U)
      naturality := sorry }

/-- The sectionwise forgetful comparison is the coefficient counit. -/
theorem weightingForgetAbelianHom_app {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etaleᵒᵖ) :
    (weightingForgetAbelianHom F).hom.app U =
      weightingAddCommGrpToModuleCounitApp (F.obj.obj U) :=
  sorry

/-- The sectionwise forgetful comparison is an isomorphism. -/
instance weightingForgetAbelianHom_isIso {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (weightingForgetAbelianHom F) :=
  sorry

/-- Forgetting `ULift ℤ`-module coefficients recovers the original abelian
étale sheaf. -/
def weightingForgetAbelianIso {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleModuleForget weightingULiftInt (weightingAbelianToModule F) ≅ F :=
  asIso (weightingForgetAbelianHom F)

/-- The forward map of `weightingForgetAbelianIso` is the sectionwise
coefficient counit. -/
theorem weightingForgetAbelianIso_hom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingForgetAbelianIso F).hom = weightingForgetAbelianHom F :=
  sorry

/-- Lift an abelian sheaf morphism between forgotten module sheaves to a
morphism of sheaves of `ULift ℤ`-modules, using the underlying additive map on
sections. -/
def weightingLiftModuleSheafHom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)}
    (α : etaleModuleForget weightingULiftInt F ⟶
      etaleModuleForget weightingULiftInt G) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦
        ConcreteCategory.ofHom (C := ModuleCat.{u} weightingULiftInt)
          { toAddHom := (α.hom.app U).hom.toAddHom
            map_smul' := fun _ _ ↦ sorry }
      naturality := sorry }

/-- The lift recovers the original abelian sheaf morphism after forgetting
coefficients. -/
theorem etaleModuleForget_map_weightingLiftModuleSheafHom {S : Scheme.{u}}
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)}
    (α : etaleModuleForget weightingULiftInt F ⟶
      etaleModuleForget weightingULiftInt G) :
    (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})).map
        (weightingLiftModuleSheafHom α) = α :=
  sorry

/-- Comparison identifying `f⁻¹` after coefficient conversion with coefficient
conversion after abelian `f⁻¹`. -/
def weightingPullbackModuleIso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u} weightingULiftInt)
          Y.smallEtaleTopology X.smallEtaleTopology).obj
        (weightingAbelianToModule F) ≅
      weightingAbelianToModule ((etaleAbelianSheafPullback f).obj F) :=
  ((Functor.sheafPullback.compSheafComposeIso (smallEtalePullback f)
      weightingAddCommGrpToModule Y.smallEtaleTopology
      X.smallEtaleTopology).app F).symm

/-- The pullback comparison is `sheafPullback.compSheafComposeIso`. -/
theorem weightingPullbackModuleIso_eq
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingPullbackModuleIso f F =
      ((Functor.sheafPullback.compSheafComposeIso (smallEtalePullback f)
          weightingAddCommGrpToModule Y.smallEtaleTopology
          X.smallEtaleTopology).app F).symm :=
  sorry

/-- Integer coefficient object as a `ULift ℤ`-module. -/
def weightingIntegerModuleCoeff : ModuleCat.{u} weightingULiftInt :=
  weightingAddCommGrpToModule.obj integerCoeff

/-- The integer coefficient module is the image of `integerCoeff`. -/
theorem weightingIntegerModuleCoeff_eq :
    weightingIntegerModuleCoeff = weightingAddCommGrpToModule.obj integerCoeff :=
  sorry

/-- Comparison of the module lift of `underline ℤ` with the constant sheaf of
the coefficient module. -/
def weightingConstantIntegerModuleIso
    (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)]
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.PreservesSheafification weightingAddCommGrpToModule] :
    weightingConstantIntegerModule S ≅
      (constantSheaf S.smallEtaleTopology
          (ModuleCat.{u} weightingULiftInt)).obj weightingIntegerModuleCoeff :=
  (constantCommuteCompose S.smallEtaleTopology
      weightingAddCommGrpToModule).app integerCoeff

/-- The comparison is the component of `constantCommuteCompose` at
`integerCoeff`. -/
theorem weightingConstantIntegerModuleIso_hom
    (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)]
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.PreservesSheafification weightingAddCommGrpToModule] :
    (weightingConstantIntegerModuleIso S).hom =
      (constantCommuteCompose S.smallEtaleTopology
          weightingAddCommGrpToModule).hom.app integerCoeff :=
  sorry

/-- The coefficient counit at `integerCoeff` is an isomorphism of abelian
groups. -/
instance weightingAddCommGrpToModuleCounitApp_integerCoeff_isIso :
    IsIso (weightingAddCommGrpToModuleCounitApp integerCoeff) :=
  sorry

/-- The coefficient module `ULift ℤ` is isomorphic to the tensor unit of
`ModuleCat (ULift ℤ)`. -/
def weightingIntegerModuleCoeffIsoTensorUnit :
    weightingIntegerModuleCoeff ≅ 𝟙_ (ModuleCat.{u} weightingULiftInt) where
  hom := ModuleCat.ofHom
    { toFun := fun x ↦ (weightingAddCommGrpToModuleCounitApp integerCoeff).hom x
      map_add' := sorry
      map_smul' := sorry }
  inv := ModuleCat.ofHom
    { toFun := fun y ↦
        ((asIso (weightingAddCommGrpToModuleCounitApp integerCoeff)).inv).hom y
      map_add' := sorry
      map_smul' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry


/-- The constant module unit is the unit of the canonical sheafified tensor.
This uses the named sheaf monoidal structure, not an arbitrary one. -/
def weightingModuleSheafTensorUnitIso (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)] :
    (constantSheaf S.smallEtaleTopology
          (ModuleCat.{u} weightingULiftInt)).obj
        (𝟙_ (ModuleCat.{u} weightingULiftInt)) ≅
      𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)) :=
  (Functor.Monoidal.εIso
    (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt))).symm

/-- The unit comparison is exactly the inverse of the canonical monoidal
unit comparison of sheafification. -/
theorem weightingModuleSheafTensorUnitIso_eq (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)] :
    weightingModuleSheafTensorUnitIso S =
      (Functor.Monoidal.εIso
        (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt))).symm := rfl

/-- The forward unit comparison is the inverse monoidal unit morphism of
sheafification. -/
theorem weightingModuleSheafTensorUnitIso_hom (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)] :
    (weightingModuleSheafTensorUnitIso S).hom =
      (Functor.Monoidal.εIso
        (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt))).inv := rfl

/-- The module lift of `underline ℤ` is isomorphic to the sheaf tensor unit. -/
def weightingConstantIntegerModuleTensorUnitIso (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)]
    [S.smallEtaleTopology.HasSheafCompose weightingAddCommGrpToModule]
    [S.smallEtaleTopology.PreservesSheafification weightingAddCommGrpToModule] :
    weightingConstantIntegerModule S ≅
      𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u} weightingULiftInt)) :=
  weightingConstantIntegerModuleIso S ≪≫
    (constantSheaf S.smallEtaleTopology
        (ModuleCat.{u} weightingULiftInt)).mapIso
      weightingIntegerModuleCoeffIsoTensorUnit ≪≫
    weightingModuleSheafTensorUnitIso S

/-- The integer trace as a morphism of sheaves of `ULift ℤ`-modules. -/
def weightingTraceIntegerModule {w : X → ℤ} (hw : f.IsWeighting w) :
    (lowerShriekModule f weightingULiftInt).obj
        (weightingConstantIntegerModule X) ⟶
      weightingConstantIntegerModule Y :=
  weightingLiftModuleSheafHom
    ((lowerShriekModule_forget f weightingULiftInt
          (weightingConstantIntegerModule X)).hom ≫
      (lowerShriek f).map (weightingForgetAbelianIso
          (etaleConstantIntegerSheaf X)).hom ≫
      weightingTraceInteger f hw ≫
      (weightingForgetAbelianIso (etaleConstantIntegerSheaf Y)).inv)

/-- The integer module trace forgets to the abelian integer trace after the
compact-support and coefficient comparisons. -/
theorem weightingTraceIntegerModule_forget {w : X → ℤ}
    (hw : f.IsWeighting w) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})).map
        (weightingTraceIntegerModule f hw) =
      (lowerShriekModule_forget f weightingULiftInt
          (weightingConstantIntegerModule X)).hom ≫
        (lowerShriek f).map (weightingForgetAbelianIso
            (etaleConstantIntegerSheaf X)).hom ≫
        weightingTraceInteger f hw ≫
        (weightingForgetAbelianIso (etaleConstantIntegerSheaf Y)).inv :=
  sorry

/-- The module-level trace on `f_! f⁻¹ F`, obtained as the image of
`Tr_ℤ ⊗ 𝟙` under the inverse of the projection comparison `can` and the
identifications `underline ℤ ⊗ f⁻¹ F ≅ f⁻¹ F` and `underline ℤ ⊗ F ≅ F`. -/
def weightingTraceModule {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekModule f weightingULiftInt).obj
        (((smallEtalePullback f).sheafPullback
            (ModuleCat.{u} weightingULiftInt)
            Y.smallEtaleTopology X.smallEtaleTopology).obj
          (weightingAbelianToModule F)) ⟶
      weightingAbelianToModule F :=
  (lowerShriekModule f weightingULiftInt).map
      ((λ_ (((smallEtalePullback f).sheafPullback
            (ModuleCat.{u} weightingULiftInt)
            Y.smallEtaleTopology X.smallEtaleTopology).obj
          (weightingAbelianToModule F))).inv ≫
        ((weightingConstantIntegerModuleTensorUnitIso X).inv ▷
          ((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} weightingULiftInt)
              Y.smallEtaleTopology X.smallEtaleTopology).obj
            (weightingAbelianToModule F))) ≫
    (lowerShriekProjectionIso f weightingULiftInt
        (weightingConstantIntegerModule X)
        (weightingAbelianToModule F)).inv ≫
    (weightingTraceIntegerModule f hw ▷ weightingAbelianToModule F) ≫
    ((weightingConstantIntegerModuleTensorUnitIso Y).hom ▷
      weightingAbelianToModule F) ≫
    (λ_ (weightingAbelianToModule F)).hom

/-- The module-level trace is `Tr_ℤ ⊗ 𝟙` conjugated by the projection
comparison and the tensor-unit identifications. -/
theorem weightingTraceModule_eq {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingTraceModule f hw F =
      (lowerShriekModule f weightingULiftInt).map
          ((λ_ (((smallEtalePullback f).sheafPullback
                (ModuleCat.{u} weightingULiftInt)
                Y.smallEtaleTopology X.smallEtaleTopology).obj
              (weightingAbelianToModule F))).inv ≫
            ((weightingConstantIntegerModuleTensorUnitIso X).inv ▷
              ((smallEtalePullback f).sheafPullback
                  (ModuleCat.{u} weightingULiftInt)
                  Y.smallEtaleTopology X.smallEtaleTopology).obj
                (weightingAbelianToModule F))) ≫
        (lowerShriekProjectionIso f weightingULiftInt
            (weightingConstantIntegerModule X)
            (weightingAbelianToModule F)).inv ≫
        (weightingTraceIntegerModule f hw ▷ weightingAbelianToModule F) ≫
        ((weightingConstantIntegerModuleTensorUnitIso Y).hom ▷
          weightingAbelianToModule F) ≫
        (λ_ (weightingAbelianToModule F)).hom :=
  sorry

/-- Comparison of the forgotten module compact-support image of `f⁻¹ F` with
the abelian compact-support image. -/
def weightingLowerShriekPullbackForgetIso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleModuleForget weightingULiftInt
        ((lowerShriekModule f weightingULiftInt).obj
          (((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} weightingULiftInt)
              Y.smallEtaleTopology X.smallEtaleTopology).obj
            (weightingAbelianToModule F))) ≅
      (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) :=
  lowerShriekModule_forget f weightingULiftInt
      (((smallEtalePullback f).sheafPullback
          (ModuleCat.{u} weightingULiftInt)
          Y.smallEtaleTopology X.smallEtaleTopology).obj
        (weightingAbelianToModule F)) ≪≫
    (lowerShriek f).mapIso
      ((Functor.sheafPullback.compSheafComposeIso (smallEtalePullback f)
            (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})
            Y.smallEtaleTopology X.smallEtaleTopology).app
          (weightingAbelianToModule F) ≪≫
        (etaleAbelianSheafPullback f).mapIso (weightingForgetAbelianIso F))

/-- The forgotten compact-support comparison is `lowerShriekModule_forget`
followed by `f_!` of the coefficient identification on `f⁻¹ F`. -/
theorem weightingLowerShriekPullbackForgetIso_hom
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingLowerShriekPullbackForgetIso f F).hom =
      (lowerShriekModule_forget f weightingULiftInt
          (((smallEtalePullback f).sheafPullback
              (ModuleCat.{u} weightingULiftInt)
              Y.smallEtaleTopology X.smallEtaleTopology).obj
            (weightingAbelianToModule F))).hom ≫
        (lowerShriek f).map
          (((Functor.sheafPullback.compSheafComposeIso (smallEtalePullback f)
                (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})
                Y.smallEtaleTopology X.smallEtaleTopology).app
              (weightingAbelianToModule F)).hom ≫
            (etaleAbelianSheafPullback f).map (weightingForgetAbelianIso F).hom) :=
  sorry

/-- Internal ModuleCat-transport construction of `Tr_{f, w, F}`. -/
def weightingTraceHomAux {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F :=
  (weightingLowerShriekPullbackForgetIso f F).inv ≫
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})).map
        (weightingTraceModule f hw F) ≫
    (weightingForgetAbelianIso F).hom

/-- The sheaf morphism `Tr_{f, w, F} : f_! f⁻¹ F ⟶ F` obtained by transporting
`Tr_ℤ ⊗ 𝟙` along `forget₂ (ModuleCat (ULift ℤ)) AddCommGrpCat` and the
projection isomorphism of Lemma 63.5.1. -/
def weightingTraceHom {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F :=
  weightingTraceHomAux f hw F

/-- The constructed trace is the forgotten image of `Tr_ℤ ⊗ 𝟙` after the
projection and coefficient comparisons. -/
theorem weightingTraceHom_eq {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    weightingTraceHom f hw F =
      (weightingLowerShriekPullbackForgetIso f F).inv ≫
        (sheafCompose Y.smallEtaleTopology
              (forget₂ (ModuleCat.{u} weightingULiftInt) AddCommGrpCat.{u})).map
            (weightingTraceModule f hw F) ≫
        (weightingForgetAbelianIso F).hom :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
