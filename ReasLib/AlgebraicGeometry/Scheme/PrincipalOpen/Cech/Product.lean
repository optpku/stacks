/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Product
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison

/-!
# Product-indexed principal-open Cech complexes

This module provides the functorial product-indexed Cech complex for a finite family of
principal opens, its totalization and canonical augmentation, and the union of the opens.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex₂
  LocalizedModule.Away TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PrincipalOpenCech

variable {A : Type u} [CommRing A] {r : ℕ}

/-- A module map induces the coordinatewise map between the tuple-indexed products of
principal localizations in Cech degree `p`. -/
noncomputable def termMap (f : Fin r → A) {M N : ModuleCat.{u, u} A}
    (g : M ⟶ N) (p : ℕ) :
    Cech.Product.term f M p ⟶ Cech.Product.term f N p :=
  ModuleCat.ofHom (LinearMap.piMap fun i ↦
    LocalizedModule.Away.map (Cech.Product.denominator f i) g.hom)

/-- The coordinatewise localized map commutes with every differential of the tuple-indexed
principal-open Cech complex. -/
theorem termMap_comm (f : Fin r → A) {M N : ModuleCat.{u, u} A}
    (g : M ⟶ N) {p q : ℕ} :
    termMap f g p ≫ (Cech.Product.complex f N).d p q =
      (Cech.Product.complex f M).d p q ≫ termMap f g q := sorry

/-- The map of tuple-indexed principal-open Cech complexes induced by a module map. -/
noncomputable def complexMap (f : Fin r → A) {M N : ModuleCat.{u, u} A}
    (g : M ⟶ N) : Cech.Product.complex f M ⟶ Cech.Product.complex f N where
  f p := termMap f g p
  comm' := fun _ _ _ ↦ termMap_comm f g

/-- The tuple-indexed Cech-complex map induced by an identity is the identity. -/
theorem complexMap_id (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    complexMap f (𝟙 M) = 𝟙 (Cech.Product.complex f M) := sorry

/-- Tuple-indexed Cech-complex maps respect composition. -/
theorem complexMap_comp (f : Fin r → A) {M N P : ModuleCat.{u, u} A}
    (g : M ⟶ N) (h : N ⟶ P) :
    complexMap f (g ≫ h) = complexMap f g ≫ complexMap f h := sorry

/-- The tuple-indexed principal-open Cech complex, functorial in its coefficient module. -/
noncomputable def complexFunctor (f : Fin r → A) :
    ModuleCat.{u, u} A ⥤ CochainComplex (ModuleCat.{u, u} A) ℕ where
  obj M := Cech.Product.complex f M
  map g := complexMap f g
  map_id := complexMap_id f
  map_comp := complexMap_comp f

/-- Evaluating the tuple-indexed Cech functor gives the explicit product-localization complex. -/
theorem complexFunctor_obj (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    (complexFunctor f).obj M = Cech.Product.complex f M := sorry

/-- Degree `p` of the tuple-indexed Cech functor is the product of the localizations indexed by
ordered `(p + 1)`-tuples. -/
theorem complexFunctor_obj_X (f : Fin r → A) (M : ModuleCat.{u, u} A) (p : ℕ) :
    ((complexFunctor f).obj M).X p = Cech.Product.term f M p := sorry

/-- Every degree of the Cech complex for the single principal open `D(f)` is isomorphic to
the localization `M[1/f]`; in particular, higher degrees are not module pushouts. -/
theorem singletonComplexTerm_isomorphic (f : Fin 1 → A)
    (M : ModuleCat.{u, u} A) (p : ℕ) :
    IsIsomorphic (((complexFunctor f).obj M).X p)
      (ModuleCat.of A (LocalizedModule.Away (f 0) M)) := sorry

/-- The canonical module-to-Cech augmentation is natural in the coefficient module. -/
theorem augmentationMap_naturality (f : Fin r → A) {M N : ModuleCat.{u, u} A}
    (g : M ⟶ N) :
    g ≫ Cech.Product.augmentationMap f N =
      Cech.Product.augmentationMap f M ≫ termMap f g 0 := sorry

/-- The tuple-indexed principal-open Cech complex, extended from `ℕ`-degrees to `ℤ`-degrees. -/
abbrev row (f : Fin r → A) :
    ModuleCat.{u, u} A ⥤ CochainComplex (ModuleCat.{u, u} A) ℤ :=
  complexFunctor f ⋙ embeddingUpNat.extendFunctor (ModuleCat.{u, u} A)

/-- The principal-open alternating Cech-row functor preserves zero morphisms. -/
instance row_preservesZeroMorphisms (f : Fin r → A) :
    (row f).PreservesZeroMorphisms := sorry

/-- The total tuple-indexed principal-open Cech functor on unbounded complexes of `A`-modules. -/
abbrev total (f : Fin r → A) :
    CochainComplex (ModuleCat.{u, u} A) ℤ ⥤
      CochainComplex (ModuleCat.{u, u} A) ℤ :=
  (row f).mapHomologicalComplex (up ℤ) ⋙
    totalFunctor (ModuleCat.{u, u} A) (up ℤ) (up ℤ) (up ℤ)

/-- The degree-zero Cech row of the tuple-indexed bicomplex of `K`. -/
abbrev zeroRow (f : Fin r → A) (K : CochainComplex (ModuleCat.{u, u} A) ℤ) :
    CochainComplex (ModuleCat.{u, u} A) ℤ :=
  ((HomologicalComplex.eval (ModuleCat.{u, u} A) (up ℤ) 0).mapHomologicalComplex (up ℤ)).obj
    (((row f).mapHomologicalComplex (up ℤ)).obj K)

/-- The natural embedding of nonnegative cochain degrees sends degree zero to degree zero. -/
theorem embeddingUpNat_zero : embeddingUpNat.f 0 = 0 := sorry

/-- The degreewise component of the augmentation into the zero Cech row. -/
noncomputable def augmentationZeroRowComponent (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u, u} A) ℤ) (n : ℤ) :
    K.X n ⟶ (zeroRow f K).X n :=
  Cech.Product.augmentationMap f (K.X n) ≫
    ((Cech.Product.complex f (K.X n)).extendXIso
      embeddingUpNat embeddingUpNat_zero).inv

/-- The degreewise tuple-indexed Cech augmentations commute with the differential of `K`. -/
theorem augmentationZeroRowComponent_comm (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u, u} A) ℤ) {n n' : ℤ}
    (hnn' : (up ℤ).Rel n n') :
    augmentationZeroRowComponent f K n ≫ (zeroRow f K).d n n' =
      K.d n n' ≫ augmentationZeroRowComponent f K n' := sorry

/-- The termwise principal-localization maps assemble to the degree-zero row of the
tuple-indexed principal-open Cech bicomplex. -/
noncomputable def augmentationZeroRow (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u, u} A) ℤ) : K ⟶ zeroRow f K where
  f n := augmentationZeroRowComponent f K n
  comm' := fun _ _ h ↦ augmentationZeroRowComponent_comm f K h

/-- The degree-zero augmentation lands in vertical cycles of the tuple-indexed Cech
bicomplex. -/
theorem augmentationZeroRow_cycles (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u, u} A) ℤ) :
    ∀ n : ℤ, (augmentationZeroRow f K).f n ≫
      ((((row f).mapHomologicalComplex (up ℤ)).obj K).X n).d 0 1 = 0 := sorry

/-- The canonical augmentation from a complex to its total tuple-indexed principal-open
Cech complex. -/
noncomputable def augmentation (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u, u} A) ℤ) : K ⟶ (total f).obj K :=
  ZeroRow.ToTotal.map (augmentationZeroRow f K) (augmentationZeroRow_cycles f K)

/-- The total tuple-indexed principal-open Cech augmentation is natural in the coefficient
complex. -/
theorem augmentation_naturality (f : Fin r → A)
    {K L : CochainComplex (ModuleCat.{u, u} A) ℤ} (g : K ⟶ L) :
    g ≫ augmentation f L = augmentation f K ≫ (total f).map g := sorry

/-- The canonical augmentation to the total tuple-indexed principal-open Cech complex. -/
noncomputable def augmentationNatTrans (f : Fin r → A) :
    Functor.id (CochainComplex (ModuleCat.{u, u} A) ℤ) ⟶ total f where
  app K := augmentation f K
  naturality := fun _ _ g ↦ augmentation_naturality f g

/-- A component of the tuple-indexed Cech augmentation is `augmentation f K`. -/
theorem augmentationNatTrans_app (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u, u} A) ℤ) :
    (augmentationNatTrans f).app K = augmentation f K := sorry

/-- The image in `Γ(Spec(A), O)` of a function cutting out a principal open. -/
abbrev globalSection (f : Fin r → A) (i : Fin r) :
    RingedSpace.globalSectionsRing (Spec (CommRingCat.of A)).toRingedSpace :=
  (ΓSpecIso (CommRingCat.of A)).inv.hom (f i)

/-- The total tuple-indexed principal-open Cech complex, viewed in `D(A)`, functorially
in a complex of modules on `Spec(A)`. -/
abbrev source (f : Fin r → A) :
    CochainComplex (Spec (CommRingCat.of A)).toRingedSpace.Modules ℤ ⥤
      DerivedCategory (ModuleCat.{u, u} A) :=
  (RingedSpace.moduleGlobalSectionsFunctor
      (Spec (CommRingCat.of A)).toRingedSpace).mapHomologicalComplex (up ℤ) ⋙
    total (globalSection f) ⋙ DerivedCategory.Q ⋙
    ModuleCat.derivedRestrictionOfScalars (ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The union of the principal opens `D(f i)` in `Spec(A)`. -/
abbrev openSubset (f : Fin r → A) : (Spec (CommRingCat.of A)).Opens :=
  ⨆ i, PrimeSpectrum.basicOpen (f i)

end AlgebraicGeometry.Scheme.PrincipalOpenCech
