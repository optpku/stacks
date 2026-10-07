module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Differential

/-!
# Module-valued Hom complexes

The homogeneous maps between two cochain complexes in an `R`-linear preadditive category form a
cochain complex of `R`-modules. This file owns that complex, its degreewise product description,
and its two-variable functoriality. Shift and closed-monoidal comparison files should import this
leaf instead of rebuilding the enriched Hom complex.
@stack 0GWQ
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedCategory
open CochainComplex.HomComplex
open scoped DifferentialGradedCategory

namespace CochainComplex.HomComplex

section Modules

variable {R : Type w} [CommRing R]

/-- The differential of a cochain complex of `R`-modules, viewed degreewise as a linear map. -/
@[stacks 0A8H "underlying differential of a module cochain complex"]
abbrev underlyingDifferential (M : CochainComplex (ModuleCat.{v} R) ℤ) :
    ∀ n : ℤ, M.X n →ₗ[R] M.X (n + 1) :=
  fun n ↦ (M.d n (n + 1)).hom

end Modules

section Linear

variable (R : Type w) [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

namespace Cochain

/-- Postcomposition with the target differential commutes with scalar multiplication. -/
theorem postDifferential_smul (M N : CochainComplex C ℤ) (n : ℤ)
    (r : R) (f : Cochain M N n) :
    postDifferential M N n (r • f) =
      r • postDifferential M N n f := sorry

/-- Precomposition with the source differential commutes with scalar multiplication. -/
theorem preDifferential_smul (M N : CochainComplex C ℤ) (n : ℤ)
    (r : R) (f : Cochain M N n) :
    preDifferential M N n (r • f) =
      r • preDifferential M N n f := sorry

end Cochain

/-- Postcomposition with the target differential as a linear map between cochain degrees. -/
@[stacks 0A8H "linear postcomposition in a Hom complex"]
def postDifferentialLinear (M N : CochainComplex C ℤ) (n : ℤ) :
    Cochain M N n →ₗ[R] Cochain M N (n + 1) where
  toFun := Cochain.postDifferential M N n
  map_add' := Cochain.postDifferential_add M N n
  map_smul' := Cochain.postDifferential_smul R M N n

/-- Precomposition with the source differential as a linear map between cochain degrees. -/
@[stacks 0A8H "linear precomposition in a Hom complex"]
def preDifferentialLinear (M N : CochainComplex C ℤ) (n : ℤ) :
    Cochain M N n →ₗ[R] Cochain M N (n + 1) where
  toFun := Cochain.preDifferential M N n
  map_add' := Cochain.preDifferential_add M N n
  map_smul' := Cochain.preDifferential_smul R M N n

/-- The degree-`n` module of the `R`-linear Hom complex `Hom^•(M, N)`. -/
@[stacks 0A8H "degree module of a module-valued Hom complex"]
abbrev moduleFamily (M N : CochainComplex C ℤ) (n : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R (Cochain M N n)

/-- The differential on the `R`-linear Hom complex `Hom^•(M, N)`. -/
@[stacks 0A8H "differential of a module-valued Hom complex"]
abbrev moduleDifferential (M N : CochainComplex C ℤ) (n : ℤ) :
    moduleFamily R M N n →ₗ[R] moduleFamily R M N (n + 1) :=
  DifferentialGradedCategory.homDifferential
    (D := CategoryTheory.CochainComplex.differentialGradedCategory C R) M N n

/-- Evaluating the enriched Hom differential is the canonical Hom-complex differential `δ`. -/
@[simp]
theorem moduleDifferential_apply (M N : CochainComplex C ℤ) (n : ℤ)
    (f : Cochain M N n) :
    moduleDifferential R M N n f = δ n (n + 1) f := sorry

/-- The enriched Hom differential is the sum of its target and source linear parts. -/
theorem moduleDifferential_eq_post_add_pre
    (M N : CochainComplex C ℤ) (n : ℤ) :
    moduleDifferential R M N n =
      postDifferentialLinear R M N n +
        (n + 1).negOnePow • preDifferentialLinear R M N n := sorry

/-- Consecutive differentials of the `R`-linear Hom complex compose to zero. -/
theorem moduleDifferential_comp (M N : CochainComplex C ℤ) (n : ℤ) :
    ModuleCat.ofHom (moduleDifferential R M N n) ≫
      ModuleCat.ofHom (moduleDifferential R M N (n + 1)) = 0 := sorry

/-- The `R`-linear Hom complex, obtained from the differential graded enrichment of cochain
complexes. -/
@[stacks 0A8H "module-valued Hom complex"]
abbrev moduleComplex (M N : CochainComplex C ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  DifferentialGradedCategory.homComplex
    (D := CategoryTheory.CochainComplex.differentialGradedCategory C R) M N

/- The scalar ring is explicit in this notation because the same pair of complexes may carry
  several linear structures.  This keeps the notation reusable outside a chapter-local alias. -/
scoped[ModuleComplex] notation:70 "⟪" M:70 ", " N:70 "⟫[" R "]" =>
  CochainComplex.HomComplex.moduleComplex R M N

/-- The degree-`n` object of the module-valued Hom complex is the module of degree-`n`
cochains. -/
@[simp]
theorem moduleComplex_X (M N : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplex R M N).X n = moduleFamily R M N n := sorry

/-- The differential of the module-valued Hom complex is `moduleDifferential`. -/
@[simp]
theorem moduleComplex_d (M N : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplex R M N).d n (n + 1) =
      ModuleCat.ofHom (moduleDifferential R M N n) := sorry

/-- The family of homogeneous maps whose product describes degree `n` of the Hom complex. -/
@[stacks 0A8H "homogeneous degree family of a Hom complex"]
abbrev degreeFamily (M N : CochainComplex C ℤ) (n : ℤ) (p : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R (M.X p ⟶ N.X (p + n))

/-- Assemble a family of homogeneous components into a degree-`n` cochain. -/
@[stacks 0A8H "assemble homogeneous Hom components"]
def familyToCochain (M N : CochainComplex C ℤ) (n : ℤ)
    (f : ∀ p : ℤ, M.X p ⟶ N.X (p + n)) : Cochain M N n :=
  Cochain.mk fun p _q hpq ↦ f p ≫ eqToHom (congrArg N.X hpq)

/-- Read the canonical homogeneous component family from a degree-`n` cochain. -/
@[stacks 0A8H "read homogeneous Hom components"]
def cochainToFamily (M N : CochainComplex C ℤ) (n : ℤ)
    (z : Cochain M N n) (p : ℤ) : M.X p ⟶ N.X (p + n) :=
  z.v p (p + n) rfl

/-- Assembling and then reading a homogeneous family is the identity. -/
theorem cochainToFamily_familyToCochain (M N : CochainComplex C ℤ) (n : ℤ)
    (f : ∀ p : ℤ, M.X p ⟶ N.X (p + n)) :
    cochainToFamily M N n (familyToCochain M N n f) = f := sorry

/-- Reading and then assembling the components of a cochain is the identity. -/
theorem familyToCochain_cochainToFamily (M N : CochainComplex C ℤ) (n : ℤ)
    (z : Cochain M N n) :
    familyToCochain M N n (cochainToFamily M N n z) = z := sorry

/-- Assembly of homogeneous component families preserves addition. -/
theorem familyToCochain_add (M N : CochainComplex C ℤ) (n : ℤ)
    (f g : ∀ p : ℤ, M.X p ⟶ N.X (p + n)) :
    familyToCochain M N n (f + g) =
      familyToCochain M N n f + familyToCochain M N n g := sorry

/-- Assembly of homogeneous component families preserves scalar multiplication. -/
theorem familyToCochain_smul (M N : CochainComplex C ℤ) (n : ℤ) (r : R)
    (f : ∀ p : ℤ, M.X p ⟶ N.X (p + n)) :
    familyToCochain M N n (r • f) = r • familyToCochain M N n f := sorry

/-- Degree-`n` cochains are linearly equivalent to their family of homogeneous components. -/
@[stacks 0A8H "homogeneous-family equivalence for Hom complexes"]
def familyLinearEquiv (M N : CochainComplex C ℤ) (n : ℤ) :
    (∀ p : ℤ, M.X p ⟶ N.X (p + n)) ≃ₗ[R] Cochain M N n where
  toFun := familyToCochain M N n
  invFun := cochainToFamily M N n
  left_inv := cochainToFamily_familyToCochain M N n
  right_inv := familyToCochain_cochainToFamily M N n
  map_add' := familyToCochain_add M N n
  map_smul' := familyToCochain_smul R M N n

/-- Evaluating an assembled homogeneous family reads its specified component. -/
@[simp]
theorem familyLinearEquiv_apply_v (M N : CochainComplex C ℤ) (n p q : ℤ)
    (f : ∀ r : ℤ, M.X r ⟶ N.X (r + n)) (hpq : p + n = q) :
    ((familyLinearEquiv R M N n) f).v p q hpq =
      f p ≫ eqToHom (congrArg N.X hpq) := sorry

/-- The inverse homogeneous-family equivalence reads the canonical component of a cochain. -/
@[simp]
theorem familyLinearEquiv_symm_apply (M N : CochainComplex C ℤ) (n p : ℤ)
    (z : Cochain M N n) :
    (familyLinearEquiv R M N n).symm z p = z.v p (p + n) rfl := sorry

/-- The canonical product decomposition of degree `n` in the module-valued Hom complex. -/
@[stacks 0A8H "degree decomposition of a module-valued Hom complex"]
noncomputable def degreeIso (M N : CochainComplex C ℤ) (n : ℤ) :
    ∏ᶜ (degreeFamily R M N n) ≅ (moduleComplex R M N).X n :=
  (ModuleCat.piIsoPi (degreeFamily R M N n)).trans
    (familyLinearEquiv R M N n).toModuleIso

/-- Projection from degree `n` of the Hom complex to its component at source degree `p`. -/
@[stacks 0A8H "homogeneous projection of a Hom complex"]
noncomputable def proj (M N : CochainComplex C ℤ) (n p : ℤ) :
    (moduleComplex R M N).X n ⟶ degreeFamily R M N n p :=
  (degreeIso R M N n).inv ≫ Pi.π (degreeFamily R M N n) p

/-- The product comparison followed by an enriched projection is the corresponding product
projection. -/
@[reassoc (attr := simp)]
theorem degreeIso_hom_proj (M N : CochainComplex C ℤ) (n p : ℤ) :
    (degreeIso R M N n).hom ≫ proj R M N n p =
      Pi.π (degreeFamily R M N n) p := sorry

/-- Applying `proj` reads the corresponding homogeneous component of a cochain. -/
@[simp]
theorem proj_apply (M N : CochainComplex C ℤ) (n p : ℤ)
    (z : (moduleComplex R M N).X n) :
    (proj R M N n p).hom z = z.v p (p + n) rfl := sorry

/-- The degree-zero cochain underlying a cochain map is closed in the canonical differential
graded category of cochain complexes. -/
theorem cochainOfHom_closed {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    (CategoryTheory.CochainComplex.differentialGradedCategory C R).d 0
      (Cochain.ofHom f) = 0 := sorry

/-- A cochain map determines a closed degree-zero morphism in the canonical differential graded
category of cochain complexes. -/
@[stacks 0A8H "closed degree-zero Hom from a cochain map"]
def closedHom {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    DifferentialGradedCategory.CompHom
      (D := CategoryTheory.CochainComplex.differentialGradedCategory C R) M N :=
  ⟨Cochain.ofHom f, cochainOfHom_closed R f⟩

/-- The underlying degree-zero cochain of `closedHom f` is `Cochain.ofHom f`. -/
@[simp]
theorem closedHom_val {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    (closedHom R f).val = Cochain.ofHom f := sorry

/-- Contravariant source and covariant target functoriality of the module-valued Hom complex. -/
@[stacks 0GWQ "map of module-valued Hom complexes"]
def map {M₁ M₂ N₁ N₂ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) :
    moduleComplex R M₁ N₁ ⟶ moduleComplex R M₂ N₂ :=
  DifferentialGradedCategory.HomComplex.precomp
      (DA := CategoryTheory.CochainComplex.differentialGradedCategory C R) (closedHom R f) ≫
    DifferentialGradedCategory.HomComplex.postcomp
      (DA := CategoryTheory.CochainComplex.differentialGradedCategory C R) (closedHom R g)

/-- The degreewise action of `map f g` is precomposition by `f` followed by postcomposition by
`g`. -/
@[simp]
theorem map_f {M₁ M₂ N₁ N₂ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) (n : ℤ) :
    (map R f g).f n =
      ModuleCat.ofHom
        (DifferentialGradedCategory.HomComplex.precompLinear
          (DA := CategoryTheory.CochainComplex.differentialGradedCategory C R)
          (closedHom R f) n) ≫
        ModuleCat.ofHom
          (DifferentialGradedCategory.HomComplex.postcompLinear
            (DA := CategoryTheory.CochainComplex.differentialGradedCategory C R)
            (closedHom R g) n) := sorry

/-- On degree-`n` cochains, `map f g` is precomposition by `f` followed by postcomposition by
`g`. -/
@[simp]
theorem map_f_apply {M₁ M₂ N₁ N₂ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) (n : ℤ) (z : Cochain M₁ N₁ n) :
    ((map R f g).f n).hom z =
      ((Cochain.ofHom f).comp z (zero_add n)).comp
        (Cochain.ofHom g) (add_zero n) := sorry

/-- Componentwise, `map f g` sends a homogeneous map to `f.f p ≫ z ≫ g.f q`. -/
@[simp]
theorem map_f_apply_v {M₁ M₂ N₁ N₂ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) (n p q : ℤ) (hpq : p + n = q)
    (z : Cochain M₁ N₁ n) :
    (((map R f g).f n).hom z).v p q hpq =
      f.f p ≫ z.v p q hpq ≫ g.f q := sorry

/-- The two-variable Hom-complex map preserves identity morphisms. -/
theorem map_id (M N : CochainComplex C ℤ) :
    map R (𝟙 M) (𝟙 N) = 𝟙 (moduleComplex R M N) := sorry

/-- The two-variable Hom-complex map preserves composition with the source variance reversed. -/
theorem map_comp
    {M₁ M₂ M₃ N₁ N₂ N₃ : CochainComplex C ℤ}
    (f : M₂ ⟶ M₁) (f' : M₃ ⟶ M₂) (g : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃) :
    map R (f' ≫ f) (g ≫ g') = map R f g ≫ map R f' g' := sorry

/-- The module-valued Hom complex as a bifunctor, contravariant in the source and covariant in
the target. -/
@[stacks 0GWQ "functorial internal Hom of module cochain complexes"]
def bifunctor :
    (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤
      CochainComplex (ModuleCat.{v} R) ℤ where
  obj X := moduleComplex R X.1.unop X.2
  map f := map R f.1.unop f.2
  map_id X := map_id R X.1.unop X.2
  map_comp f g := map_comp R f.1.unop g.1.unop f.2 g.2

/-- The module-valued Hom-complex bifunctor in curried form. -/
@[stacks 0GWQ "curried module-valued Hom-complex bifunctor"]
def curried :
    (CochainComplex C ℤ)ᵒᵖ ⥤
      CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  Functor.curry.obj (bifunctor R)

end Linear

end CochainComplex.HomComplex
