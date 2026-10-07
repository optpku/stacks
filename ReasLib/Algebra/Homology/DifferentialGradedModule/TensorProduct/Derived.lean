module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative derived tensor product of differential graded modules

This file derives the universe-polymorphic relative tensor complex directly.  For a left
DG `A`-module represented as a right DG `A.opposite`-module, it first derives tensoring in the
right-module variable.  Naturality in the left variable then descends through its own
quasi-isomorphism localization.  The resulting public bifunctor has type
`D(A) ⥤ D(A.opposite) ⥤ D(R)` and does not require an auxiliary same-universe bimodule.
-/

@[expose] public section

noncomputable section

universe u x v w

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.TensorProduct.Derived

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

namespace FixedLeft

/-- Tensoring a represented homotopy class with a fixed left module is independent of its
closed degree-zero representative. -/
theorem source_map_sound
    (N : DifferentialGradedModule.{u, w} A.opposite)
    {M M' : DifferentialGradedModule.{u, v} A} {f g : CompHom M M'}
    (h : DifferentialGradedCategory.Homotopic M M' f g) :
    DerivedCategory.Q.map
        (TensorProduct.mapRight (LeftDifferentialGradedModule.unop N)
          (DifferentialGradedModule.compHomToHom f)) =
      DerivedCategory.Q.map
        (TensorProduct.mapRight (LeftDifferentialGradedModule.unop N)
          (DifferentialGradedModule.compHomToHom g)) := sorry

/-- The homotopy-level tensor source with a fixed left DG module, valued in the ordinary
derived category of `R`-modules. -/
noncomputable def source
    (N : DifferentialGradedModule.{u, w} A.opposite) :
    K R (DifferentialGradedModule.{u, v} A) ⥤
      DerivedCategory (ModuleCat.{max v w} R) where
  obj M := DerivedCategory.Q.obj
    (TensorProduct.complex M.obj (LeftDifferentialGradedModule.unop N))
  map {M M'} f := Quotient.lift
    (fun g : CompHom M.obj M'.obj ↦ DerivedCategory.Q.map
      (TensorProduct.mapRight (LeftDifferentialGradedModule.unop N)
        (DifferentialGradedModule.compHomToHom g)))
    (fun _ _ h ↦ source_map_sound N h) f
  map_id := sorry
  map_comp := sorry

/-- The fixed-left source evaluates to the localization of the explicit relative tensor
complex. -/
@[simp]
theorem source_obj (N : DifferentialGradedModule.{u, w} A.opposite)
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (source N).obj M = DerivedCategory.Q.obj
      (TensorProduct.complex M.obj (LeftDifferentialGradedModule.unop N)) := sorry

/-- On an ordinary DG-module map, the fixed-left source is localization of the explicit map
on relative tensor complexes. -/
@[simp]
theorem source_map_toK (N : DifferentialGradedModule.{u, w} A.opposite)
    {M M' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M') :
    (source N).map ((DifferentialGradedModule.toK A).map f) =
      DerivedCategory.Q.map
        (TensorProduct.mapRight (LeftDifferentialGradedModule.unop N) f) := sorry

/-- Property-(P) resolutions make fixed-left relative tensor source-defined at every object. -/
@[stacks 0GZI "existence of fixed-left relative derived tensor"]
instance sourceEverywhereDefined
    (N : DifferentialGradedModule.{u, w} A.opposite) :
    Functor.LeftDerived.EverywhereDefined (source N)
      (DifferentialGradedModule.quasiIso A) := sorry

/-- Fixed-left relative tensor admits Mathlib's canonical total left-derived functor. -/
instance sourceHasLeftDerivedFunctor
    (N : DifferentialGradedModule.{u, w} A.opposite) :
    (source N).HasLeftDerivedFunctor
      (DifferentialGradedModule.quasiIso A) := sorry

/-- The relative derived tensor functor in the right-module variable, for a fixed left
DG-module representative. -/
@[stacks 0GZI "relative derived tensor with a fixed left DG module",
  stacks 0GZJ "relative derived tensor with a powered Koszul module"]
noncomputable def functor
    (N : DifferentialGradedModule.{u, w} A.opposite) :
    DifferentialGradedModule.Derived.Category.{u, v} A ⥤
      DerivedCategory (ModuleCat.{max v w} R) :=
  (source N).totalLeftDerived
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A)

/-- The canonical comparison from fixed-left relative derived tensor to the localized explicit
tensor source. -/
noncomputable def counit
    (N : DifferentialGradedModule.{u, w} A.opposite) :
    DifferentialGradedModule.Derived.Q A ⋙ functor N ⟶ source N :=
  (source N).totalLeftDerivedCounit
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A)

/-- The chosen fixed-left functor and comparison satisfy the universal property of the total
left-derived functor. -/
noncomputable instance functorIsLeftDerived
    (N : DifferentialGradedModule.{u, w} A.opposite) :
    (functor N).IsLeftDerivedFunctor (counit N)
      (DifferentialGradedModule.quasiIso A) := sorry

/-- A morphism of left DG-module representatives induces a natural transformation between the
homotopy-level fixed-left tensor sources. -/
def sourceMap
    {N N' : DifferentialGradedModule.{u, w} A.opposite} (f : N ⟶ N') :
    source N ⟶ source N' where
  app M := DerivedCategory.Q.map
    (TensorProduct.mapLeft M.obj
      ((LeftDifferentialGradedModule.unopFunctor A).map f))
  naturality := sorry

/-- A morphism of left DG-module representatives induces the canonical transformation between
the corresponding fixed-left relative derived tensor functors. -/
noncomputable def map
    {N N' : DifferentialGradedModule.{u, w} A.opposite} (f : N ⟶ N') :
    functor N ⟶ functor N' :=
  Functor.leftDerivedNatTrans (functor N) (functor N')
    (counit N) (counit N') (DifferentialGradedModule.quasiIso A) (sourceMap f)

/-- The fixed-left source transformation is functorial on identities. -/
@[simp]
theorem sourceMap_id (N : DifferentialGradedModule.{u, w} A.opposite) :
    sourceMap (𝟙 N) = 𝟙 (source N) := sorry

/-- The fixed-left source transformation preserves composition. -/
@[simp]
theorem sourceMap_comp
    {L M N : DifferentialGradedModule.{u, w} A.opposite}
    (f : L ⟶ M) (g : M ⟶ N) :
    sourceMap (f ≫ g) = sourceMap f ≫ sourceMap g := sorry

/-- The transformation on fixed-left relative derived tensor is functorial on identities. -/
@[simp]
theorem map_id (N : DifferentialGradedModule.{u, w} A.opposite) :
    map (𝟙 N) = 𝟙 (functor N) := sorry

/-- The transformation on fixed-left relative derived tensor preserves composition. -/
@[simp]
theorem map_comp
    {L M N : DifferentialGradedModule.{u, w} A.opposite}
    (f : L ⟶ M) (g : M ⟶ N) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Homotopic maps of left DG-module representatives induce the same transformation on
fixed-left relative derived tensor functors. -/
theorem map_sound
    {N N' : DifferentialGradedModule.{u, w} A.opposite} {f g : CompHom N N'}
    (h : DifferentialGradedCategory.Homotopic N N' f g) :
    map (DifferentialGradedModule.compHomToHom f) =
      map (DifferentialGradedModule.compHomToHom g) := sorry

end FixedLeft

namespace LeftFactor

/-- The homotopy-level functor of the left tensor factor, with values in functors out of
`D(A)`. -/
noncomputable def source (A : CochainDGAlgebra.{u, x} R) :
    K R (DifferentialGradedModule.{u, w} A.opposite) ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} A ⥤
        DerivedCategory (ModuleCat.{max v w} R)) where
  obj N := FixedLeft.functor N.obj
  map {N N'} f := Quotient.lift
    (fun g : CompHom N.obj N'.obj ↦
      FixedLeft.map (DifferentialGradedModule.compHomToHom g))
    (fun _ _ h ↦ FixedLeft.map_sound h) f
  map_id := sorry
  map_comp := sorry

/-- The homotopy-level left-factor functor sends quasi-isomorphisms to natural isomorphisms. -/
@[stacks 0GZI "relative derived tensor inverts left-factor quasi-isomorphisms"]
theorem source_inverts (A : CochainDGAlgebra.{u, x} R) :
    (DifferentialGradedModule.quasiIso A.opposite).IsInvertedBy
      (source A) := sorry

/-- Relative derived tensor descended through quasi-isomorphisms in its left-module factor. -/
@[stacks 0GZI "descent of relative derived tensor in the left factor"]
noncomputable def functor (A : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedModule.Derived.Category.{u, w} A.opposite ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} A ⥤
        DerivedCategory (ModuleCat.{max v w} R)) :=
  Localization.lift (source A) (source_inverts A)
    (DifferentialGradedModule.Derived.Q A.opposite)

/-- Before localization in the left factor, the descended relative derived tensor functor
recovers the fixed-representative construction. -/
noncomputable def factorizationIso (A : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedModule.Derived.Q A.opposite ⋙ functor A ≅
      source A :=
  Localization.fac (source A) (source_inverts A)
    (DifferentialGradedModule.Derived.Q A.opposite)

/-- The left-factor relative derived tensor functor is registered as the canonical lift of its
homotopy-level source. -/
@[stacks 0GZI "lifting property of relative derived tensor in the left factor"]
noncomputable instance functorLifting (A : CochainDGAlgebra.{u, x} R) :
    Localization.Lifting
      (DifferentialGradedModule.Derived.Q A.opposite)
      (DifferentialGradedModule.quasiIso A.opposite)
      (source.{u, x, v, w} A) (functor A) :=
  ⟨factorizationIso A⟩

end LeftFactor

/-- The universe-polymorphic relative derived tensor bifunctor
`D(A) ⥤ D(A.opposite) ⥤ D(R)`. -/
@[stacks 0GZI "relative derived tensor bifunctor",
  stacks 0GZJ "relative derived tensor for powered Koszul systems"]
noncomputable def functor (A : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedModule.Derived.Category.{u, v} A ⥤
      DifferentialGradedModule.Derived.Category.{u, w} A.opposite ⥤
        DerivedCategory (ModuleCat.{max v w} R) :=
  (LeftFactor.functor A).flip

/-- The value of the relative derived tensor bifunctor on a right and a left derived
DG-module. -/
noncomputable abbrev obj (A : CochainDGAlgebra.{u, x} R)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (N : DifferentialGradedModule.Derived.Category.{u, w} A.opposite) :
    DerivedCategory (ModuleCat.{max v w} R) :=
  ((functor A).obj M).obj N

/-- Evaluating the relative derived tensor bifunctor agrees with the left-factor localization
before flipping the variables. -/
@[simp]
theorem functor_obj_obj (A : CochainDGAlgebra.{u, x} R)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (N : DifferentialGradedModule.Derived.Category.{u, w} A.opposite) :
    obj A M N = ((LeftFactor.functor A).obj N).obj M := sorry

/-- On a represented left factor, relative derived tensor is canonically the fixed-left
derived tensor functor. -/
@[stacks 0GZI "factorization of relative derived tensor on a representative"]
noncomputable def factorizationIso (A : CochainDGAlgebra.{u, x} R)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (N : K R (DifferentialGradedModule.{u, w} A.opposite)) :
    obj A M ((DifferentialGradedModule.Derived.Q A.opposite).obj N) ≅
      (FixedLeft.functor N.obj).obj M :=
  ((LeftFactor.factorizationIso A).app N).app M

/-- Scoped notation for the relative derived tensor object over a cochain DGA. -/
scoped[TensorProduct] notation:70 M:70 " ⊗ᴸ[" A "] " N:71 =>
  DifferentialGradedModule.TensorProduct.Derived.obj A M N

end DifferentialGradedModule.TensorProduct.Derived
