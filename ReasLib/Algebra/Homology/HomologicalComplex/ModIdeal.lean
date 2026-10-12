/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing

/-!
# Homological complexes modulo an ideal

Quotienting a module by the multiples of an ideal is functorial, hence may be applied termwise to
any homological complex.  This file provides the explicit quotient-complex model and identifies it
naturally with extension of scalars along the quotient map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace HomologicalComplex.ModIdeal

variable {A : Type u} [CommRing A]
variable {ι : Type w} {c : ComplexShape ι}

/-- The degree-`i` term of a homological complex modulo `I`. -/
def term (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    ModuleCat.{v} (A ⧸ I) :=
  ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i)))

/-- The linear map induced modulo `I` by the differential from degree `i` to degree `j`. -/
def dLinear (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i j : ι) :
    term I K i →ₗ[A ⧸ I] term I K j :=
  LinearMap.IdealQuotient.map (K.d i j).hom I

/-- The differential of the explicit quotient complex. -/
def d (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i j : ι) :
    term I K i ⟶ term I K j :=
  ModuleCat.ofHom (dLinear I K i j)

/-- On quotient representatives, the quotient differential is induced by the original
differential. -/
@[simp]
theorem d_mk (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c)
    (i j : ι) (x : K.X i) :
    (d I K i j).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((K.d i j).hom x) := sorry

/-- The quotient differential vanishes outside the shape of the original complex. -/
theorem d_shape (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c)
    (i j : ι) (hij : ¬c.Rel i j) : d I K i j = 0 := sorry

/-- Two successive quotient differentials compose to zero. -/
theorem d_comp_d (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c)
    (i j k : ι) : d I K i j ≫ d I K j k = 0 := sorry

/-- The explicit homological complex obtained by quotienting every term by the multiples of `I`. -/
@[stacks 00DV "homological complexes modulo an ideal"]
def complex (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) :
    HomologicalComplex (ModuleCat.{v} (A ⧸ I)) c where
  X i := term I K i
  d i j := d I K i j
  shape i j hij := d_shape I K i j hij
  d_comp_d' i j k _ _ := d_comp_d I K i j k

/-- The degree-`i` object of the quotient complex is the corresponding module quotient. -/
@[simp]
theorem complex_X (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    (complex I K).X i = term I K i := sorry

/-- The differential of the quotient complex is the induced quotient map. -/
@[simp]
theorem complex_d (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i j : ι) :
    (complex I K).d i j = d I K i j := sorry

/-- The degree-`i` map induced modulo `I` by a morphism of homological complexes. -/
def mapLinear (I : Ideal A) {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : K ⟶ L) (i : ι) : term I K i →ₗ[A ⧸ I] term I L i :=
  LinearMap.IdealQuotient.map (φ.f i).hom I

/-- The degreewise quotient maps commute with the quotient differentials. -/
theorem map_comm (I : Ideal A) {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    ModuleCat.ofHom (mapLinear I φ i) ≫ (complex I L).d i j =
      (complex I K).d i j ≫ ModuleCat.ofHom (mapLinear I φ j) := sorry

/-- The morphism induced after quotienting a homological complex termwise by `I`. -/
@[stacks 00DV "maps of homological complexes modulo an ideal"]
def map (I : Ideal A) {K L : HomologicalComplex (ModuleCat.{v} A) c} (φ : K ⟶ L) :
    complex I K ⟶ complex I L where
  f i := ModuleCat.ofHom (mapLinear I φ i)
  comm' i j hij := map_comm I φ i j hij

/-- On quotient representatives, the induced map is the quotient class of the original map. -/
@[simp]
theorem map_mk (I : Ideal A) {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : K ⟶ L) (i : ι) (x : K.X i) :
    (map I φ).f i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ.f i x) := sorry

/-- Termwise quotienting preserves identity morphisms of homological complexes. -/
@[simp]
theorem map_id (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) :
    map I (𝟙 K) = 𝟙 (complex I K) := sorry

/-- Termwise quotienting preserves composition of morphisms of homological complexes. -/
@[simp]
theorem map_comp (I : Ideal A) {K L M : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : K ⟶ L) (ψ : L ⟶ M) : map I (φ ≫ ψ) = map I φ ≫ map I ψ := sorry

/-- The functor that quotients homological complexes termwise by the multiples of `I`. -/
@[stacks 00DV "termwise quotient functor on homological complexes"]
def functor (I : Ideal A) :
    HomologicalComplex (ModuleCat.{v} A) c ⥤
      HomologicalComplex (ModuleCat.{v} (A ⧸ I)) c where
  obj K := complex I K
  map φ := map I φ
  map_id K := map_id I K
  map_comp φ ψ := map_comp I φ ψ

/-- The termwise quotient complex, regarded again as a complex of `A`-modules by restriction of
scalars along `A ⟶ A ⧸ I`. -/
abbrev restrictedComplex (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) :
    HomologicalComplex (ModuleCat.{v} A) c :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex c).obj
    (complex I K)

/-- A morphism of complexes modulo `I`, regarded as an `A`-linear morphism after restricting
scalars. -/
abbrev restrictedMap (I : Ideal A) {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : K ⟶ L) : restrictedComplex I K ⟶ restrictedComplex I L :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex c).map (map I φ)

/-- Termwise quotienting followed by restriction from `A ⧸ I` to `A`. -/
@[stacks 00DV "scalar-restricted termwise quotient functor"]
abbrev restrictedFunctor (I : Ideal A) :
    HomologicalComplex (ModuleCat.{v} A) c ⥤ HomologicalComplex (ModuleCat.{v} A) c :=
  functor I ⋙
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex c

/-- The canonical projection from one term of a complex to its quotient by `I`, viewed after
restriction of scalars back to `A`. -/
def projectionLinear (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    K.X i →ₗ[A] (restrictedComplex I K).X i :=
  Submodule.mkQ (I • (⊤ : Submodule A (K.X i)))

/-- The termwise quotient projections commute with the differentials. -/
theorem projection_comm (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c)
    (i j : ι) (hij : c.Rel i j) :
    ModuleCat.ofHom (X := K.X i) (Y := (restrictedComplex I K).X i)
          (projectionLinear I K i) ≫
        (restrictedComplex I K).d i j =
      K.d i j ≫ ModuleCat.ofHom (X := K.X j) (Y := (restrictedComplex I K).X j)
        (projectionLinear I K j) := sorry

/-- The canonical morphism from a homological complex to its termwise quotient by `I`, regarded
as a complex over the original ring. -/
@[stacks 00DV "projection to a termwise quotient complex"]
def projection (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) :
    K ⟶ restrictedComplex I K where
  f i := ModuleCat.ofHom (X := K.X i) (Y := (restrictedComplex I K).X i)
    (projectionLinear I K i)
  comm' i j hij := projection_comm I K i j hij

/-- The quotient projection sends an element to its quotient class. -/
@[simp]
theorem projection_apply (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c)
    (i : ι) (x : K.X i) :
    (projection I K).f i x = Submodule.Quotient.mk x := sorry

/-- Every component of the termwise quotient projection is surjective. -/
theorem projection_surjective (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c)
    (i : ι) : Function.Surjective ((projection I K).f i) := sorry

/-- Projection to a termwise quotient is natural in the homological complex. -/
theorem projection_naturality (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (φ : K ⟶ L) :
    φ ≫ projection I L = projection I K ≫ restrictedMap I φ := sorry

/-- Projection to the termwise quotient is natural in the homological complex. -/
@[stacks 00DV "natural projection to a termwise quotient complex"]
def projectionNatTrans (I : Ideal A) :
    𝟭 (HomologicalComplex (ModuleCat.{v} A) c) ⟶ restrictedFunctor I where
  app K := projection I K
  naturality _ _ φ := projection_naturality I φ

/-- Extension of scalars along `A ⟶ A ⧸ I`, applied to homological complexes. -/
abbrev extension (I : Ideal A) :
    HomologicalComplex (ModuleCat.{max u v} A) c ⥤
      HomologicalComplex (ModuleCat.{max u v} (A ⧸ I)) c :=
  (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)).mapHomologicalComplex c

/-- In each degree, extension to `A ⧸ I` is canonically the quotient by the multiples of `I`. -/
def extensionTermIso (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) (i : ι) :
    ((extension.{u, v, w} I).obj K).X i ≅ (complex I K).X i :=
  (Ideal.Quotient.tensorModuleEquiv I (K.X i)).toModuleIso

/-- The degreewise tensor-quotient identifications commute with the differentials. -/
theorem extensionTermIso_hom_comm (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) (i j : ι) (hij : c.Rel i j) :
    (extensionTermIso.{u, v, w} I K i).hom ≫ (complex I K).d i j =
      ((extension.{u, v, w} I).obj K).d i j ≫
        (extensionTermIso.{u, v, w} I K j).hom := sorry

/-- The canonical comparison from scalar extension to the explicit quotient-complex model. -/
def extensionComparison (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    (extension.{u, v, w} I).obj K ⟶ complex I K where
  f i := (extensionTermIso.{u, v, w} I K i).hom
  comm' i j hij := extensionTermIso_hom_comm.{u, v, w} I K i j hij

/-- The inverses of the degreewise tensor-quotient identifications commute with differentials. -/
theorem extensionTermIso_inv_comm (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) (i j : ι) (hij : c.Rel i j) :
    (extensionTermIso.{u, v, w} I K i).inv ≫ ((extension.{u, v, w} I).obj K).d i j =
      (complex I K).d i j ≫ (extensionTermIso.{u, v, w} I K j).inv := sorry

/-- The inverse comparison from the explicit quotient complex to scalar extension. -/
def extensionComparisonInv (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    complex I K ⟶ (extension.{u, v, w} I).obj K where
  f i := (extensionTermIso.{u, v, w} I K i).inv
  comm' i j hij := extensionTermIso_inv_comm.{u, v, w} I K i j hij

/-- The scalar-extension comparison followed by its explicit inverse is the identity. -/
theorem extensionComparison_hom_inv_id (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    extensionComparison.{u, v, w} I K ≫ extensionComparisonInv.{u, v, w} I K =
      𝟙 ((extension.{u, v, w} I).obj K) := sorry

/-- The explicit inverse followed by the scalar-extension comparison is the identity. -/
theorem extensionComparison_inv_hom_id (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    extensionComparisonInv.{u, v, w} I K ≫ extensionComparison.{u, v, w} I K =
      𝟙 (complex I K) := sorry

/-- Scalar extension to `A ⧸ I` is canonically isomorphic to the explicit termwise quotient
complex. -/
@[stacks 00DV "scalar extension as a termwise quotient complex"]
def extensionIso (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    (extension.{u, v, w} I).obj K ≅ complex I K where
  hom := extensionComparison.{u, v, w} I K
  inv := extensionComparisonInv.{u, v, w} I K
  hom_inv_id := extensionComparison_hom_inv_id.{u, v, w} I K
  inv_hom_id := extensionComparison_inv_hom_id.{u, v, w} I K

/-- The scalar-extension comparison is natural in the homological complex. -/
theorem extensionComparison_naturality (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{max u v} A) c} (φ : K ⟶ L) :
    (extension.{u, v, w} I).map φ ≫ extensionComparison.{u, v, w} I L =
      extensionComparison.{u, v, w} I K ≫ map I φ := sorry

/-- The scalar-extension comparisons assemble into a natural transformation. -/
def extensionNatTrans (I : Ideal A) :
    extension.{u, v, w} (c := c) I ⟶ functor.{u, max u v, w} (c := c) I where
  app K := extensionComparison.{u, v, w} I K
  naturality _ _ φ := extensionComparison_naturality.{u, v, w} I φ

/-- The inverse scalar-extension comparison is natural in the homological complex. -/
theorem extensionComparisonInv_naturality (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{max u v} A) c} (φ : K ⟶ L) :
    map I φ ≫ extensionComparisonInv.{u, v, w} I L =
      extensionComparisonInv.{u, v, w} I K ≫ (extension.{u, v, w} I).map φ := sorry

/-- The inverse scalar-extension comparisons assemble into a natural transformation. -/
def extensionNatTransInv (I : Ideal A) :
    functor.{u, max u v, w} (c := c) I ⟶ extension.{u, v, w} (c := c) I where
  app K := extensionComparisonInv.{u, v, w} I K
  naturality _ _ φ := extensionComparisonInv_naturality.{u, v, w} I φ

/-- The comparison and inverse natural transformations compose to the identity. -/
theorem extensionNatTrans_hom_inv_id (I : Ideal A) :
    extensionNatTrans.{u, v, w} (c := c) I ≫
        extensionNatTransInv.{u, v, w} (c := c) I =
      𝟙 (extension.{u, v, w} (c := c) I) := sorry

/-- The inverse and comparison natural transformations compose to the identity. -/
theorem extensionNatTrans_inv_hom_id (I : Ideal A) :
    extensionNatTransInv.{u, v, w} (c := c) I ≫
        extensionNatTrans.{u, v, w} (c := c) I =
      𝟙 (functor.{u, max u v, w} (c := c) I) := sorry

/-- Termwise quotienting by `I` is naturally isomorphic to extension of scalars along the quotient
map `A ⟶ A ⧸ I`. -/
@[stacks 00DV "termwise quotient is extension of scalars"]
def extensionNatIso (I : Ideal A) :
    extension.{u, v, w} (c := c) I ≅ functor.{u, max u v, w} (c := c) I where
  hom := extensionNatTrans.{u, v, w} (c := c) I
  inv := extensionNatTransInv.{u, v, w} (c := c) I
  hom_inv_id := extensionNatTrans_hom_inv_id.{u, v, w} (c := c) I
  inv_hom_id := extensionNatTrans_inv_hom_id.{u, v, w} (c := c) I

/-- The forward component of the extension-quotient natural isomorphism is the explicit
comparison map. -/
@[simp]
theorem extensionNatIso_hom_app (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    (extensionNatIso.{u, v, w} (c := c) I).hom.app K =
      extensionComparison.{u, v, w} I K := sorry

/-- The inverse component of the extension-quotient natural isomorphism is the explicit inverse
comparison map. -/
@[simp]
theorem extensionNatIso_inv_app (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{max u v} A) c) :
    (extensionNatIso.{u, v, w} (c := c) I).inv.app K =
      extensionComparisonInv.{u, v, w} I K := sorry

end HomologicalComplex.ModIdeal
