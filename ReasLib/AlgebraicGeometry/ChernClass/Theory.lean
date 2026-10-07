module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Topology.Clopen
public import ReasLib.AlgebraicGeometry.ChernClass.ProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/-- The open complement of a clopen subscheme. -/
def clopenComplement {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClopen (U : Set X)) : X.Opens :=
  ⟨(U : Set X)ᶜ, hU.compl.isOpen⟩

/-- The carrier of `clopenComplement U hU` is the complement of the carrier of `U`. -/
theorem coe_clopenComplement {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClopen (U : Set X)) :
    (clopenComplement U hU : Set X) = (U : Set X)ᶜ := sorry

/-- The Picard class of the tautological invertible module of a projective bundle. -/
noncomputable def tautologicalPicardClass {X P : Scheme.{u}} (p : P ⟶ X)
    (E : X.Modules) (hP : Scheme.ProjectiveBundle.Representation p E) :
    P.PicardGroup :=
  @Scheme.Modules.picardClass P
    (Scheme.ProjectiveBundle.tautologicalSheaf p hP)
    (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p hP)

/-- The tautological Picard class is represented by the tautological invertible module. -/
theorem tautologicalPicardClass_eq {X P : Scheme.{u}} (p : P ⟶ X)
    (E : X.Modules) (hP : Scheme.ProjectiveBundle.Representation p E) :
    tautologicalPicardClass p E hP =
      @Scheme.Modules.picardClass P
        (Scheme.ProjectiveBundle.tautologicalSheaf p hP)
        (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p hP) := sorry

/-- The geometric and cohomological data of a category of qcqs schemes closed under clopen
restrictions and the required projective-bundle morphisms, together with a contravariant
nonnegatively graded ring theory and a first Chern class satisfying the Chern-class axioms. -/
structure Theory
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)] where
  /-- Every scheme in the source category is quasi-compact. -/
  compactSpace : ∀ X, CompactSpace (toScheme.obj X)
  /-- Every scheme in the source category is quasi-separated. -/
  quasiSeparatedSpace : ∀ X, QuasiSeparatedSpace (toScheme.obj X)
  /-- The homogeneous pieces exhaust the cohomology ring. -/
  grading_isInternal : ∀ X, DirectSum.IsInternal (Agrade X)
  /-- Pullback preserves every homogeneous degree. -/
  pullback_mem : ∀ {X' X : C} (f : X' ⟶ X) (i : ℕ) (a : Agrade X i),
    A.map f.op a ∈ Agrade X' i
  /-- The object of the category presenting a clopen subscheme. -/
  clopenObject : ∀ (X : C) (U : (toScheme.obj X).Opens),
    IsClopen (U : Set (toScheme.obj X)) → C
  /-- The chosen category object really presents the clopen subscheme. -/
  clopenIso : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    toScheme.obj (clopenObject X U hU) ≅ U.toScheme
  /-- The clopen inclusion is a morphism of the source category. -/
  clopenInclusion : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    clopenObject X U hU ⟶ X
  /-- The chosen clopen inclusion maps to the usual scheme inclusion. -/
  clopenInclusion_map : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    toScheme.map (clopenInclusion X U hU) = (clopenIso X U hU).hom ≫ U.ι
  /-- A source-category morphism factoring through a clopen subscheme has a factor in the
  source category. -/
  clopenFactor : ∀ {X' X : C} (f : X' ⟶ X) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X)))
      (g : toScheme.obj X' ⟶ U.toScheme),
    g ≫ U.ι = toScheme.map f → (X' ⟶ clopenObject X U hU)
  /-- The chosen categorical factor maps to the given factor through the clopen subscheme. -/
  clopenFactor_map : ∀ {X' X : C} (f : X' ⟶ X)
      (U : (toScheme.obj X).Opens) (hU : IsClopen (U : Set (toScheme.obj X)))
      (g : toScheme.obj X' ⟶ U.toScheme) (h_g : g ≫ U.ι = toScheme.map f),
    toScheme.map (clopenFactor f U hU g h_g) = g ≫ (clopenIso X U hU).inv
  /-- Cohomology takes a decomposition into complementary clopen subschemes to a product. -/
  clopenProduct : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    Function.Bijective fun a : A.obj (Opposite.op X) ↦
      (A.map (clopenInclusion X U hU).op a,
        A.map (clopenInclusion X (clopenComplement U hU) hU.compl).op a)
  /-- The object presenting the projective bundle of a finite locally free module. -/
  projectiveBundle : ∀ (X : C),
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules) → C
  /-- The projection from the chosen projective bundle. -/
  projectiveBundleProjection : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    projectiveBundle X E ⟶ X
  /-- The chosen projection represents the projective bundle of `E`. -/
  projectiveBundleRepresentation : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    Scheme.ProjectiveBundle.Representation
      (toScheme.map (projectiveBundleProjection X E)) E.obj
  /-- Base change of a projective bundle is a morphism in the source category. -/
  projectiveBundlePullback : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    projectiveBundle X'
        (Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E) ⟶
      projectiveBundle X E
  /-- The projective-bundle base-change morphism lies over the original morphism. -/
  projectiveBundlePullback_comm : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    toScheme.map (projectiveBundlePullback f E) ≫
        toScheme.map (projectiveBundleProjection X E) =
      toScheme.map (projectiveBundleProjection X'
        (Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E)) ≫ toScheme.map f
  /-- The square defining projective-bundle base change is cartesian. -/
  projectiveBundlePullback_isPullback : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    IsPullback (toScheme.map (projectiveBundlePullback f E))
      (toScheme.map (projectiveBundleProjection X'
        (Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E)))
      (toScheme.map (projectiveBundleProjection X E)) (toScheme.map f)
  /-- A quotient of finite locally free modules induces a morphism of projective bundles in
  the source category. -/
  projectiveBundleQuotient : ∀ {X : C}
      {E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)}
      (q : E ⟶ F), Epi q → (projectiveBundle X F ⟶ projectiveBundle X E)
  /-- The projective-bundle morphism induced by a quotient is a closed immersion. -/
  projectiveBundleQuotient_isClosed : ∀ {X : C}
      {E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)}
      (q : E ⟶ F) (h_q : Epi q),
    IsClosedImmersion (toScheme.map (projectiveBundleQuotient q h_q))
  /-- The additive first Chern class with values in degree one. -/
  firstChernClass : ∀ X, (toScheme.obj X).PicardGroup →+ Agrade X 1
  /-- First Chern classes are central in the cohomology algebra. -/
  firstChernClass_central : ∀ (X : C) (L : (toScheme.obj X).PicardGroup)
      (a : A.obj (Opposite.op X)),
    (firstChernClass X L : A.obj (Opposite.op X)) * a =
      a * (firstChernClass X L : A.obj (Opposite.op X))
  /-- First Chern classes commute with pullback. -/
  firstChernClass_naturality : ∀ {X' X : C} (f : X' ⟶ X)
      (L : (toScheme.obj X).PicardGroup),
    A.map f.op (firstChernClass X L : A.obj (Opposite.op X)) =
      (firstChernClass X'
        (Scheme.Hom.picardPullback (toScheme.map f) L) : A.obj (Opposite.op X'))
  /-- The projective-bundle map for a rank-`r` bundle. -/
  projectiveBundleEquiv : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ), Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj →
    (Fin r → A.obj (Opposite.op X)) ≃
      A.obj (Opposite.op (projectiveBundle X E))
  /-- The projective-bundle equivalence is the sum of pullbacks multiplied by powers of the
  tautological first Chern class. -/
  projectiveBundleEquiv_apply : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj)
      (a : Fin r → A.obj (Opposite.op X)),
    projectiveBundleEquiv X E r h_E a =
      ∑ i : Fin r,
        (firstChernClass (projectiveBundle X E)
          (tautologicalPicardClass
            (toScheme.map (projectiveBundleProjection X E)) E.obj
            (projectiveBundleRepresentation X E)) :
              A.obj (Opposite.op (projectiveBundle X E))) ^ i.1 *
          A.map (projectiveBundleProjection X E).op (a i)
  /-- The Picard class of the effective Cartier divisor induced by a quotient of ranks
  `r + 1` and `r`. -/
  quotientDivisorClass : ∀ (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F), Epi q →
    (toScheme.obj (projectiveBundle X E)).PicardGroup
  /-- The projective-bundle inclusion induced by a rank-one quotient is an effective Cartier
  divisor. -/
  quotient_isEffectiveCartier : ∀ (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q),
    IsEffectiveCartierDivisor (toScheme.map (projectiveBundleQuotient q h_q))
  /-- The chosen quotient-divisor class is the Picard class of the associated invertible
  sheaf of the actual projective-bundle divisor. -/
  quotientDivisorClass_spec : ∀ (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q),
    quotientDivisorClass X E F r h_E h_F q h_q =
      @Scheme.Modules.picardClass (toScheme.obj (projectiveBundle X E))
        (@Scheme.effectiveCartierDivisorAssociatedSheaf
          (toScheme.obj (projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩)
        (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible
          (toScheme.obj (projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩)
  /-- A class vanishing on the quotient divisor is annihilated by its first Chern class. -/
  cartierVanishing : ∀ (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q)
      (a : A.obj (Opposite.op (projectiveBundle X E))),
    A.map (projectiveBundleQuotient q h_q).op a = 0 →
      a * (firstChernClass (projectiveBundle X E)
        (quotientDivisorClass X E F r h_E h_F q h_q) :
          A.obj (Opposite.op (projectiveBundle X E))) = 0

namespace Theory

/-- The quotient-divisor class in a theory is canonically the Picard class of the associated
invertible sheaf of the effective Cartier divisor. -/
theorem quotientDivisorClass_eq
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {A : Cᵒᵖ ⥤ RingCat.{x}}
    {Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))}
    [∀ X, GradedAlgebra (Agrade X)] (S : Theory toScheme A Agrade)
    (X : C)
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
    (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
    (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
    (q : E ⟶ F) (h_q : Epi q) :
    S.quotientDivisorClass X E F r h_E h_F q h_q =
      @Scheme.Modules.picardClass (toScheme.obj (S.projectiveBundle X E))
        (@Scheme.effectiveCartierDivisorAssociatedSheaf
          (toScheme.obj (S.projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (S.projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (S.quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩)
        (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible
          (toScheme.obj (S.projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (S.projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (S.quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩) := sorry

/-- Assemble a cohomological theory from its geometric data and Chern-class axioms. -/
def ofAxioms := @Theory.mk

end Theory

end AlgebraicGeometry.ChernClass
