module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of scalars for relative derived tensor products

The ordinary comparison from a tensor product of restricted DG modules to the tensor product
over the target DGA is first derived in the right-module variable.  Its naturality in the left
factor then descends through the canonical localization.  The resulting `mapOver` API composes
maps living over a DGA homomorphism without exposing resolutions or localization choices.
-/

@[expose] public section

noncomputable section

universe u x v w

open CategoryTheory DifferentialGradedCategory

namespace DifferentialGradedModule.TensorProduct.Derived

variable {R : Type u} [CommRing R]
variable {A B C : CochainDGAlgebra.{u, x} R}

namespace FixedLeft

/-- The homotopy-level source obtained by restricting both tensor factors along `φ`. -/
def restrictionSource (φ : A ⟶ B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    K R (DifferentialGradedModule.{u, v} B) ⥤
      DerivedCategory (ModuleCat.{max v w} R) :=
  φ.restrictDgFunctor.mapK ⋙
    source (φ.opposite.restrictModule N)

/-- The ordinary restriction comparison, localized in the target category, gives a map from
the restricted homotopy-level tensor source to the source over the target DGA. -/
@[stacks 0GZI "homotopy-level restriction comparison for relative derived tensor"]
def restrictionSourceMap (φ : A ⟶ B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    restrictionSource.{u, x, v, w} φ N ⟶ source N where
  app M := DerivedCategory.Q.map
    (DifferentialGradedModule.TensorProduct.restrictMap φ M.obj N)
  naturality := sorry

/-- Relative derived tensor over `A` after derived restriction of the right factor from `B`,
with a fixed restricted left DG-module representative. -/
noncomputable def restrictedFunctor (φ : A ⟶ B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    DifferentialGradedModule.Derived.Category.{u, v} B ⥤
      DerivedCategory (ModuleCat.{max v w} R) :=
  CochainDGAlgebra.Hom.Derived.restriction φ ⋙
    functor (φ.opposite.restrictModule N)

/-- The comparison from the restricted derived tensor candidate to its homotopy-level
restriction source. -/
noncomputable def restrictedCounit (φ : A ⟶ B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    DifferentialGradedModule.Derived.Q B ⋙
        restrictedFunctor.{u, x, v, w} φ N ⟶
      restrictionSource φ N where
  app M :=
    (functor (φ.opposite.restrictModule N)).map
        ((CochainDGAlgebra.Hom.Derived.restrictionFac φ).hom.app M) ≫
      (counit (φ.opposite.restrictModule N)).app
        ((φ.restrictDgFunctor.mapK).obj M)
  naturality := sorry

/-- The canonical restriction comparison for relative derived tensor with a fixed left
DG-module representative. -/
@[stacks 0GZI "fixed-left restriction comparison for relative derived tensor"]
noncomputable def restrictionMap (φ : A ⟶ B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    restrictedFunctor.{u, x, v, w} φ N ⟶ functor N :=
  Functor.leftDerivedNatTrans
    (restrictedFunctor φ N) (functor N)
    (restrictedCounit φ N) (counit N)
    (DifferentialGradedModule.quasiIso B) (restrictionSourceMap φ N)

/-- The fixed-left derived restriction comparison is characterized by the universal
left-derived comparison square. -/
theorem restrictionMap_fac (φ : A ⟶ B)
    (N : DifferentialGradedModule.{u, w} B.opposite) :
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q B)
          (restrictionMap.{u, x, v, w} φ N) ≫
        counit N =
      restrictedCounit φ N ≫ restrictionSourceMap φ N := sorry

end FixedLeft

namespace LeftFactor

/-- The left-factor homotopy source for tensoring after restricting both factors along `φ`. -/
noncomputable def restrictedSource (φ : A ⟶ B) :
    K R (DifferentialGradedModule.{u, w} B.opposite) ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} B ⥤
        DerivedCategory (ModuleCat.{max v w} R)) :=
  φ.opposite.restrictDgFunctor.mapK ⋙
    LeftFactor.source A ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (CochainDGAlgebra.Hom.Derived.restriction φ)

/-- Fixed-left restriction comparisons form a natural transformation in the represented left
factor. -/
def restrictionSourceMap (φ : A ⟶ B) :
    restrictedSource.{u, x, v, w} φ ⟶ LeftFactor.source B where
  app N := FixedLeft.restrictionMap φ N.obj
  naturality := sorry

/-- Relative derived tensor after applying derived restriction to both inputs, organized in
the left-factor order used for localization. -/
noncomputable def restrictedFunctor (φ : A ⟶ B) :
    DifferentialGradedModule.Derived.Category.{u, w} B.opposite ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} B ⥤
        DerivedCategory (ModuleCat.{max v w} R)) :=
  CochainDGAlgebra.Hom.Derived.restriction φ.opposite ⋙
    LeftFactor.functor A ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (CochainDGAlgebra.Hom.Derived.restriction φ)

/-- The restricted left-factor functor canonically factors its represented homotopy source. -/
@[stacks 0GZI "factorization of restricted relative derived tensor"]
noncomputable def restrictedFactorizationIso (φ : A ⟶ B) :
    DifferentialGradedModule.Derived.Q B.opposite ⋙
        restrictedFunctor.{u, x, v, w} φ ≅
      restrictedSource φ where
  hom :=
    { app := fun N ↦
        Functor.whiskerLeft (CochainDGAlgebra.Hom.Derived.restriction φ)
          ((LeftFactor.functor A).map
              ((CochainDGAlgebra.Hom.Derived.restrictionFac φ.opposite).hom.app N) ≫
            (LeftFactor.factorizationIso A).hom.app
              ((φ.opposite.restrictDgFunctor.mapK).obj N))
      naturality := sorry }
  inv :=
    { app := fun N ↦
        Functor.whiskerLeft (CochainDGAlgebra.Hom.Derived.restriction φ)
          ((LeftFactor.factorizationIso A).inv.app
                ((φ.opposite.restrictDgFunctor.mapK).obj N) ≫
            (LeftFactor.functor A).map
              ((CochainDGAlgebra.Hom.Derived.restrictionFac φ.opposite).inv.app N))
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The restricted left-factor functor is the canonical localization lift of its homotopy
source. -/
noncomputable instance restrictedLifting (φ : A ⟶ B) :
    Localization.Lifting
      (DifferentialGradedModule.Derived.Q B.opposite)
      (DifferentialGradedModule.quasiIso B.opposite)
      (restrictedSource.{u, x, v, w} φ) (restrictedFunctor φ) :=
  ⟨restrictedFactorizationIso φ⟩

/-- The restriction comparison descended through the left-factor localization. -/
@[stacks 0GZI "restriction comparison for the relative derived tensor bifunctor"]
noncomputable def restrictionMap (φ : A ⟶ B) :
    restrictedFunctor.{u, x, v, w} φ ⟶ LeftFactor.functor B :=
  Localization.liftNatTrans
    (DifferentialGradedModule.Derived.Q B.opposite)
    (DifferentialGradedModule.quasiIso B.opposite)
    (restrictedSource φ) (LeftFactor.source B)
    (restrictedFunctor φ) (LeftFactor.functor B)
    (restrictionSourceMap φ)

end LeftFactor

/-- Relative derived tensor over `A` after restricting both inputs from `B`. -/
@[stacks 0GZI "relative derived tensor after restriction of both factors"]
noncomputable def restrictedFunctor (φ : A ⟶ B) :
    DifferentialGradedModule.Derived.Category.{u, v} B ⥤
      DifferentialGradedModule.Derived.Category.{u, w} B.opposite ⥤
        DerivedCategory (ModuleCat.{max v w} R) :=
  (LeftFactor.restrictedFunctor φ).flip

/-- The canonical natural transformation from relative derived tensor after restriction to
relative derived tensor over the target DGA. -/
@[stacks 0GZI "change-of-scalars comparison for relative derived tensor"]
noncomputable def restrictNatTrans (φ : A ⟶ B) :
    restrictedFunctor.{u, x, v, w} φ ⟶ functor B :=
  (flipFunctor _ _ _).map (LeftFactor.restrictionMap φ)

/-- The component of the change-of-scalars comparison on two derived DG modules. -/
@[stacks 0GZI "restriction map for relative derived tensor objects"]
noncomputable abbrev restrictMap (φ : A ⟶ B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} B)
    (N : DifferentialGradedModule.Derived.Category.{u, w} B.opposite) :
    obj A
          ((CochainDGAlgebra.Hom.Derived.restriction φ).obj M)
          ((CochainDGAlgebra.Hom.Derived.restriction φ.opposite).obj N) ⟶
      obj B M N :=
  (restrictNatTrans φ).app M |>.app N

/-- Maps of both tensor factors over a DGA homomorphism induce a map of relative derived tensor
objects. -/
@[stacks 0GZI "maps over a DGA homomorphism on relative derived tensor"]
noncomputable def mapOver (φ : A ⟶ B)
    {M : DifferentialGradedModule.Derived.Category.{u, v} A}
    {M' : DifferentialGradedModule.Derived.Category.{u, v} B}
    {N : DifferentialGradedModule.Derived.Category.{u, w} A.opposite}
    {N' : DifferentialGradedModule.Derived.Category.{u, w} B.opposite}
    (f : M ⟶ (CochainDGAlgebra.Hom.Derived.restriction φ).obj M')
    (g : N ⟶ (CochainDGAlgebra.Hom.Derived.restriction φ.opposite).obj N') :
    obj A M N ⟶ obj B M' N' :=
  ((functor A).map f).app N ≫
    ((functor A).obj
      ((CochainDGAlgebra.Hom.Derived.restriction φ).obj M')).map g ≫
      restrictMap φ M' N'

/-- `mapOver` along an identity DGA map is ordinary bifunctoriality after the canonical
identity restriction comparisons are removed. -/
theorem mapOver_id (A : CochainDGAlgebra.{u, x} R)
    {M M' : DifferentialGradedModule.Derived.Category.{u, v} A}
    {N N' : DifferentialGradedModule.Derived.Category.{u, w} A.opposite}
    (f : M ⟶ (CochainDGAlgebra.Hom.Derived.restriction
      (𝟙 A : CochainDGAlgebra.Hom A A)).obj M')
    (g : N ⟶ (CochainDGAlgebra.Hom.Derived.restriction
      ((CochainDGAlgebra.oppositeFunctor R).map
        (𝟙 A : CochainDGAlgebra.Hom A A))).obj N') :
    mapOver (𝟙 A : CochainDGAlgebra.Hom A A) f g =
      ((functor A).map
          (f ≫ (CochainDGAlgebra.Hom.Derived.restrictionIdIso A).inv.app M')).app N ≫
        ((functor A).obj M').map
          (g ≫ (CochainDGAlgebra.Hom.Derived.opRestrictionIdIso A).inv.app N') := sorry

/-- The canonical identity restriction comparisons give the identity map under `mapOver`. -/
@[simp]
theorem mapOver_refl (A : CochainDGAlgebra.{u, x} R)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (N : DifferentialGradedModule.Derived.Category.{u, w} A.opposite) :
    mapOver (𝟙 A : CochainDGAlgebra.Hom A A)
        ((CochainDGAlgebra.Hom.Derived.restrictionIdIso A).hom.app M)
        ((CochainDGAlgebra.Hom.Derived.opRestrictionIdIso A).hom.app N) =
      CategoryStruct.id (obj A M N) := sorry

/-- `mapOver` respects composition of DGA homomorphisms and of maps over those
homomorphisms. -/
theorem mapOver_comp (φ : A ⟶ B) (ψ : B ⟶ C)
    {M : DifferentialGradedModule.Derived.Category.{u, v} A}
    {M' : DifferentialGradedModule.Derived.Category.{u, v} B}
    {M'' : DifferentialGradedModule.Derived.Category.{u, v} C}
    {N : DifferentialGradedModule.Derived.Category.{u, w} A.opposite}
    {N' : DifferentialGradedModule.Derived.Category.{u, w} B.opposite}
    {N'' : DifferentialGradedModule.Derived.Category.{u, w} C.opposite}
    (f : M ⟶ (CochainDGAlgebra.Hom.Derived.restriction φ).obj M')
    (f' : M' ⟶ (CochainDGAlgebra.Hom.Derived.restriction ψ).obj M'')
    (g : N ⟶ (CochainDGAlgebra.Hom.Derived.restriction φ.opposite).obj N')
    (g' : N' ⟶ (CochainDGAlgebra.Hom.Derived.restriction ψ.opposite).obj N'') :
    mapOver φ f g ≫ mapOver ψ f' g' =
      mapOver (φ ≫ ψ)
        (f ≫ (CochainDGAlgebra.Hom.Derived.restriction φ).map f' ≫
          (CochainDGAlgebra.Hom.Derived.restrictionCompIso φ ψ).hom.app M'')
        (g ≫ (CochainDGAlgebra.Hom.Derived.restriction φ.opposite).map g' ≫
          (CochainDGAlgebra.Hom.Derived.opRestrictionCompIso φ ψ).hom.app N'') := sorry

end DifferentialGradedModule.TensorProduct.Derived
