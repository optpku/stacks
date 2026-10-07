module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import stacks_project.Chap56.Lemma_56_5_2_Admissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The stalk functor of a quasicoherent module at a point of `X`. -/
noncomputable def stalkFunctor (X : Scheme.{u}) (x : X) :
    Scheme.QCoh X ⥤ ModuleCat (X.ringCatSheaf.presheaf.stalk x) :=
  Scheme.QCoh.inclusion X ⋙ SheafOfModules.stalkFunctor X.ringCatSheaf x

/-- Taking stalks of quasicoherent modules preserves zero morphisms. -/
instance stalkFunctor_preservesZeroMorphisms (X : Scheme.{u}) (x : X) :
    (stalkFunctor X x).PreservesZeroMorphisms := sorry

/-- The short complex of stalks of a short complex of quasicoherent modules. -/
noncomputable def stalkShortComplex {X : Scheme.{u}}
    (S : ShortComplex (Scheme.QCoh X)) (x : X) :
    ShortComplex (ModuleCat (X.ringCatSheaf.presheaf.stalk x)) :=
  S.map (stalkFunctor X x)

/-- Images of composable morphisms with zero composite remain zero. -/
theorem map_comp_eq_zero (F : Scheme.QCoh X ⥤ Scheme.QCoh Y)
    {A B C : Scheme.QCoh X} (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) :
    F.map f ≫ F.map g = 0 := sorry

/-- Exactness of `0 ⟶ A ⟶ B ⟶ C` as a (not necessarily epi) sequence. -/
def IsTruncatedExact {A B C : Scheme.QCoh Y} (f : A ⟶ B) (g : B ⟶ C)
    (h : f ≫ g = 0) : Prop :=
  Mono f ∧ (ShortComplex.mk f g h).Exact

/-- Truncated exactness unpacks as monicity of the first map together with
exactness of the short complex. -/
theorem isTruncatedExact_iff {A B C : Scheme.QCoh Y} (f : A ⟶ B) (g : B ⟶ C)
    (h : f ≫ g = 0) :
    IsTruncatedExact f g h ↔
      Mono f ∧ (ShortComplex.mk f g h).Exact := sorry

/-- A short exact sequence of quasicoherent modules that splits after taking
stalks at every point of `X`. -/
def IsStalkwiseSplitExact {X : Scheme.{u}} (S : ShortComplex (Scheme.QCoh X)) : Prop :=
  S.ShortExact ∧ ∀ x : X, Nonempty (stalkShortComplex S x).Splitting

/-- An `R`-linear functor of quasicoherent modules that preserves arbitrary
coproducts, is right exact after composition with pushforward from affine
opens, and preserves exactness of stalkwise-split short exact sequences. -/
class AffineOpenCoproductLinear (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) : Prop
    extends LinearOver x y F where
  preservesCoproducts : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F
  affineOpen_rightExact :
    ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsAffine U] [IsOpenImmersion j]
      [QuasiCompact j] [QuasiSeparated j],
      rightExactFunctor (Scheme.QCoh U) (Scheme.QCoh Y)
        (@pushforward U X j _ _ ⋙ F)
  preservesStalkwiseSplitExact :
    ∀ {A B C : Scheme.QCoh X} (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0),
      IsStalkwiseSplitExact (ShortComplex.mk f g hfg) →
        IsTruncatedExact (F.map f) (F.map g) (map_comp_eq_zero F f g hfg)

/-- Affine-open coproduct-linearity unpacks as relative `R`-linearity, coproduct
preservation, affine-open right exactness of `F ∘ j_*`, and exactness on
stalkwise-split sequences. -/
theorem affineOpenCoproductLinear_iff (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) :
    AffineOpenCoproductLinear x y F ↔
      LinearOver x y F ∧
        (∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) ∧
          (∀ {U : Scheme.{u}} (j : U ⟶ X) [IsAffine U] [IsOpenImmersion j]
            [QuasiCompact j] [QuasiSeparated j],
            rightExactFunctor (Scheme.QCoh U) (Scheme.QCoh Y)
              (@pushforward U X j _ _ ⋙ F)) ∧
            ∀ {A B C : Scheme.QCoh X} (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0),
              IsStalkwiseSplitExact (ShortComplex.mk f g hfg) →
                IsTruncatedExact (F.map f) (F.map g)
                  (map_comp_eq_zero F f g hfg) := sorry

/-- The category of affine-open coproduct-linear functors
`Scheme.QCoh X ⥤ Scheme.QCoh Y`. -/
abbrev AffineOpenCoproductLinearFunctor (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) :=
  ObjectProperty.FullSubcategory
    fun F : Scheme.QCoh X ⥤ Scheme.QCoh Y ↦ AffineOpenCoproductLinear x y F

/-- Objects of `AffineOpenCoproductLinearFunctor` are affine-open
coproduct-linear functors. -/
theorem affineOpenCoproductLinearFunctor_property
    (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
    (F : AffineOpenCoproductLinearFunctor x y) :
    AffineOpenCoproductLinear x y F.obj := F.property

end AlgebraicGeometry.Scheme.QCoh
