/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.QuasiIso
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Naturality of relative tensor product in the bimodule variable

A morphism of differential graded `(A, B)`-bimodules induces the concrete map
`M ⊗_A N ⟶ M ⊗_A N'`. These maps assemble into natural transformations on the closed and
intrinsic homotopy categories. On a property-P source, a bimodule quasi-isomorphism induces a
quasi-isomorphism of tensor products.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable {N N' N'' : DifferentialGradedBimodule.{u, w, x, y} A B}

/-- A bimodule morphism induces the ordinary right DG `B`-module map
`M ⊗_A N ⟶ M ⊗_A N'` by acting on the second tensor factor. -/
@[stacks 09S3 "underived tensor map in the bimodule variable"]
def mapBimodule (M : DifferentialGradedModule.{u, v} A) (f : N ⟶ N') :
    obj M N ⟶ obj M N' where
  hom n := DifferentialGradedModule.TensorProduct.mapLeftLinear M
    (DifferentialGradedBimodule.Hom.toLeftHom f) n
  comm_d := sorry
  comm_smul := sorry

/-- The map induced by a bimodule morphism sends a pure tensor to the pure tensor obtained by
applying that morphism in the second factor. -/
@[simp]
theorem mapBimodule_tmul (M : DifferentialGradedModule.{u, v} A) (f : N ⟶ N')
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    (mapBimodule M f).hom (p + q) (tmul M N m x) =
      tmul M N' m (f.hom q x) := sorry

/-- Acting by the identity bimodule morphism gives the identity tensor map. -/
@[simp]
theorem mapBimodule_id (M : DifferentialGradedModule.{u, v} A)
    (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    mapBimodule M (𝟙 N) = 𝟙 (obj M N) := sorry

/-- Acting on the bimodule factor preserves composition. -/
@[simp]
theorem mapBimodule_comp (M : DifferentialGradedModule.{u, v} A)
    (f : N ⟶ N') (g : N' ⟶ N'') :
    mapBimodule M (f ≫ g) = mapBimodule M f ≫ mapBimodule M g := sorry

/-- Tensoring a sum of bimodule morphisms acts by the sum of the induced maps. -/
@[simp]
theorem mapBimodule_add (M : DifferentialGradedModule.{u, v} A)
    (f g : N ⟶ N') :
    mapBimodule M (f + g) = mapBimodule M f + mapBimodule M g := sorry

/-- Tensoring a scalar multiple of a bimodule morphism acts by the corresponding scalar
multiple. -/
@[simp]
theorem mapBimodule_smul (M : DifferentialGradedModule.{u, v} A)
    (r : R) (f : N ⟶ N') :
    mapBimodule M (r • f) = r • mapBimodule M f := sorry

/-- The tensor maps in the bimodule variable are natural in closed degree-zero morphisms of the
first tensor factor. -/
@[stacks 09LN "naturality of closed tensor maps in the bimodule"]
theorem sourceComp_naturality (f : N ⟶ N')
    {M M' : Comp R (DifferentialGradedModule.{u, v} A)} (g : M ⟶ M') :
    (dgFunctor.{u, v, w, x, y} N).mapComp.map g ≫
        DifferentialGradedModule.homToCompHom (mapBimodule M'.obj f) =
      DifferentialGradedModule.homToCompHom (mapBimodule M.obj f) ≫
        (dgFunctor.{u, v, w, x, y} N').mapComp.map g := sorry

/-- A bimodule morphism induces a natural transformation between the corresponding tensor
functors on closed degree-zero morphisms. -/
@[stacks 09LN "closed tensor transformation in the bimodule variable"]
def sourceComp (f : N ⟶ N') :
    (dgFunctor.{u, v, w, x, y} N).mapComp ⟶ (dgFunctor.{u, v, w, x, y} N').mapComp where
  app M := DifferentialGradedModule.homToCompHom (mapBimodule M.obj f)
  naturality := fun {M M'} g ↦
    sourceComp_naturality (N := N) (N' := N') f (M := M) (M' := M') g

/-- A component of the closed tensor transformation is represented by the explicit map on the
bimodule tensor factor. -/
@[simp, stacks 09LN "component of the closed tensor transformation"]
theorem sourceComp_app (f : N ⟶ N')
    (M : Comp R (DifferentialGradedModule.{u, v} A)) :
    (sourceComp f).app M =
      DifferentialGradedModule.homToCompHom (mapBimodule M.obj f) := sorry

/-- The component on an intrinsic homotopy-category object induced by a bimodule morphism.
Keeping this representative-level datum separate lets downstream natural transformations reuse
the same explicit homotopy class without unfolding the closed tensor functors. -/
@[stacks 09LT "component of the homotopy tensor transformation"]
def sourceKApp (f : N ⟶ N')
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (dgFunctor.{u, v, w, x, y} N).mapK.obj M ⟶ (dgFunctor.{u, v, w, x, y} N').mapK.obj M :=
  (DifferentialGradedModule.homToCompHom (mapBimodule M.obj f)).inK

/-- The explicit homotopy component agrees with the component obtained from the closed tensor
transformation. -/
@[simp]
theorem sourceKApp_eq_sourceComp (f : N ⟶ N')
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    sourceKApp f M = ((sourceComp f).app
      (⟨M.obj⟩ : Comp R (DifferentialGradedModule.{u, v} A))).inK := sorry

/-- The tensor maps in the bimodule variable remain natural after passing to homotopy classes.
-/
@[stacks 09LT "naturality of homotopy tensor maps in the bimodule"]
theorem sourceK_naturality (f : N ⟶ N')
    {M M' : K R (DifferentialGradedModule.{u, v} A)} (g : M ⟶ M') :
    (dgFunctor.{u, v, w, x, y} N).mapK.map g ≫ sourceKApp f M' =
      sourceKApp f M ≫ (dgFunctor.{u, v, w, x, y} N').mapK.map g := sorry

/-- A bimodule morphism induces a natural transformation between the corresponding tensor
functors on intrinsic DG homotopy categories. -/
@[stacks 09LT "homotopy tensor transformation in the bimodule variable"]
def sourceK (f : N ⟶ N') : (dgFunctor.{u, v, w, x, y} N).mapK ⟶ (dgFunctor.{u, v, w, x, y} N').mapK where
  app M := sourceKApp f M
  naturality := fun {M M'} g ↦
    sourceK_naturality (N := N) (N' := N') f (M := M) (M' := M') g

/-- The homotopy-category component of the tensor transformation is represented by the
concrete closed tensor map. -/
@[simp]
theorem sourceK_app (f : N ⟶ N')
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (sourceK f).app M = sourceKApp f M := sorry

/-- On a represented DG module, the homotopy tensor transformation is the homotopy class of
the explicit tensor map. -/
@[simp]
theorem sourceK_app_toK (f : N ⟶ N')
    (M : DifferentialGradedModule.{u, v} A) :
    (sourceK f).app ((DifferentialGradedModule.toK A).obj M) =
      (DifferentialGradedModule.toK B).map (mapBimodule M f) := sorry

/-- The identity bimodule morphism induces the identity closed tensor transformation. -/
@[simp]
theorem sourceComp_id (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    sourceComp (𝟙 N) = 𝟙 (dgFunctor.{u, v, w, x, y} N).mapComp := sorry

/-- Closed tensor transformations preserve composition of bimodule morphisms. -/
@[simp]
theorem sourceComp_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    sourceComp (f ≫ g) = sourceComp f ≫ sourceComp g := sorry

/-- Closed tensor transformations are additive in the bimodule morphism. -/
@[simp]
theorem sourceComp_add (f g : N ⟶ N') :
    sourceComp (f + g) = sourceComp f + sourceComp g := sorry

/-- Closed tensor transformations are `R`-linear in the bimodule morphism. -/
@[simp]
theorem sourceComp_smul (r : R) (f : N ⟶ N') :
    sourceComp (r • f) = r • sourceComp f := sorry

/-- The identity bimodule morphism induces the identity homotopy tensor transformation. -/
@[simp]
theorem sourceK_id (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    sourceK (𝟙 N) = 𝟙 (dgFunctor.{u, v, w, x, y} N).mapK := sorry

/-- Homotopy tensor transformations preserve composition of bimodule morphisms. -/
@[simp]
theorem sourceK_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    sourceK (f ≫ g) = sourceK f ≫ sourceK g := sorry

/-- Homotopy tensor transformations are additive in the bimodule morphism. -/
@[simp]
theorem sourceK_add (f g : N ⟶ N') :
    sourceK (f + g) = sourceK f + sourceK g := sorry

/-- Homotopy tensor transformations are `R`-linear in the bimodule morphism. -/
@[simp]
theorem sourceK_smul (r : R) (f : N ⟶ N') :
    sourceK (r • f) = r • sourceK f := sorry

namespace Closed

/-- Closed tensor functors, functorially parametrized by the differential graded bimodule. -/
@[stacks 09LN "closed DG tensor functor parametrized by the bimodule"]
def bimoduleFunctor :
    DifferentialGradedBimodule.{u, w, x, y} A B ⥤
      (Comp R (DifferentialGradedModule.{u, v} A) ⥤
        Comp R (DifferentialGradedModule.{u, max v w} B)) where
  obj N := (dgFunctor.{u, v, w, x, y} N).mapComp
  map f := sourceComp f
  map_id := sorry
  map_comp := sorry

/-- Evaluating the closed bimodule-parameter tensor functor gives the fixed-bimodule functor. -/
@[simp]
theorem bimoduleFunctor_obj (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (bimoduleFunctor (A := A) (B := B)).obj N = (dgFunctor.{u, v, w, x, y} N).mapComp := sorry

/-- The closed bimodule-parameter tensor functor maps a morphism by `sourceComp`. -/
@[simp]
theorem bimoduleFunctor_map {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f : N ⟶ N') :
    (bimoduleFunctor (A := A) (B := B)).map f = sourceComp f := sorry

/-- The closed tensor parameter functor preserves addition of bimodule morphisms. -/
@[simp]
theorem bimoduleFunctor_map_add
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f g : N ⟶ N') :
    (bimoduleFunctor (A := A) (B := B)).map (f + g) =
      (bimoduleFunctor (A := A) (B := B)).map f +
        (bimoduleFunctor (A := A) (B := B)).map g := sorry

/-- The closed tensor parameter functor is additive. -/
@[stacks 09LN "additive closed DG tensor parameter functor"]
instance bimoduleFunctorAdditive :
    (bimoduleFunctor (A := A) (B := B)).Additive := sorry

/-- The closed tensor parameter functor preserves scalar multiplication of bimodule
morphisms. -/
@[simp]
theorem bimoduleFunctor_map_smul
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (r : R) (f : N ⟶ N') :
    (bimoduleFunctor (A := A) (B := B)).map (r • f) =
      r • (bimoduleFunctor (A := A) (B := B)).map f := sorry

/-- The closed tensor parameter functor is `R`-linear. -/
@[stacks 09LN "linear closed DG tensor parameter functor"]
instance bimoduleFunctorLinear :
    Functor.Linear R (bimoduleFunctor (A := A) (B := B)) := sorry

end Closed

namespace Homotopy

/-- Homotopy tensor functors, functorially parametrized by the differential graded bimodule. -/
@[stacks 09LT "homotopy DG tensor functor parametrized by the bimodule"]
def bimoduleFunctor :
    DifferentialGradedBimodule.{u, w, x, y} A B ⥤
      (K R (DifferentialGradedModule.{u, v} A) ⥤
        K R (DifferentialGradedModule.{u, max v w} B)) where
  obj N := (dgFunctor.{u, v, w, x, y} N).mapK
  map f := sourceK f
  map_id := sorry
  map_comp := sorry

/-- Evaluating the homotopy bimodule-parameter tensor functor gives the fixed-bimodule functor. -/
@[simp]
theorem bimoduleFunctor_obj (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (bimoduleFunctor (A := A) (B := B)).obj N = (dgFunctor.{u, v, w, x, y} N).mapK := sorry

/-- The homotopy bimodule-parameter tensor functor maps a morphism by `sourceK`. -/
@[simp]
theorem bimoduleFunctor_map {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f : N ⟶ N') :
    (bimoduleFunctor (A := A) (B := B)).map f = sourceK f := sorry

/-- The homotopy tensor parameter functor preserves addition of bimodule morphisms. -/
@[simp]
theorem bimoduleFunctor_map_add
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f g : N ⟶ N') :
    (bimoduleFunctor (A := A) (B := B)).map (f + g) =
      (bimoduleFunctor (A := A) (B := B)).map f +
        (bimoduleFunctor (A := A) (B := B)).map g := sorry

/-- The homotopy tensor parameter functor is additive. -/
@[stacks 09LT "additive homotopy DG tensor parameter functor"]
instance bimoduleFunctorAdditive :
    (bimoduleFunctor (A := A) (B := B)).Additive := sorry

/-- The homotopy tensor parameter functor preserves scalar multiplication of bimodule
morphisms. -/
@[simp]
theorem bimoduleFunctor_map_smul
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (r : R) (f : N ⟶ N') :
    (bimoduleFunctor (A := A) (B := B)).map (r • f) =
      r • (bimoduleFunctor (A := A) (B := B)).map f := sorry

/-- The homotopy tensor parameter functor is `R`-linear. -/
@[stacks 09LT "linear homotopy DG tensor parameter functor"]
instance bimoduleFunctorLinear :
    Functor.Linear R (bimoduleFunctor (A := A) (B := B)) := sorry

end Homotopy

/-- The closed tensor transformations induced by the two maps of a bimodule isomorphism are
inverse. -/
theorem sourceCompIso_hom_inv_id (e : N ≅ N') :
    sourceComp e.hom ≫ sourceComp e.inv = 𝟙 (dgFunctor.{u, v, w, x, y} N).mapComp := sorry

/-- The inverse and forward closed tensor transformations induced by a bimodule isomorphism are
inverse. -/
theorem sourceCompIso_inv_hom_id (e : N ≅ N') :
    sourceComp e.inv ≫ sourceComp e.hom = 𝟙 (dgFunctor.{u, v, w, x, y} N').mapComp := sorry

/-- A bimodule isomorphism induces a natural isomorphism between tensor functors on closed
degree-zero morphisms. -/
@[stacks 09LN "closed tensor isomorphism in the bimodule variable"]
def sourceCompIso (e : N ≅ N') : (dgFunctor.{u, v, w, x, y} N).mapComp ≅ (dgFunctor.{u, v, w, x, y} N').mapComp where
  hom := sourceComp e.hom
  inv := sourceComp e.inv
  hom_inv_id := sourceCompIso_hom_inv_id e
  inv_hom_id := sourceCompIso_inv_hom_id e

/-- The homotopy tensor transformations induced by the two maps of a bimodule isomorphism are
inverse. -/
theorem sourceKIso_hom_inv_id (e : N ≅ N') :
    sourceK e.hom ≫ sourceK e.inv = 𝟙 (dgFunctor.{u, v, w, x, y} N).mapK := sorry

/-- The inverse and forward homotopy tensor transformations induced by a bimodule isomorphism
are inverse. -/
theorem sourceKIso_inv_hom_id (e : N ≅ N') :
    sourceK e.inv ≫ sourceK e.hom = 𝟙 (dgFunctor.{u, v, w, x, y} N').mapK := sorry

/-- A bimodule isomorphism induces a natural isomorphism between tensor functors on intrinsic
DG homotopy categories. -/
@[stacks 09LT "homotopy tensor isomorphism in the bimodule variable"]
def sourceKIso (e : N ≅ N') : (dgFunctor.{u, v, w, x, y} N).mapK ≅ (dgFunctor.{u, v, w, x, y} N').mapK where
  hom := sourceK e.hom
  inv := sourceK e.inv
  hom_inv_id := sourceKIso_hom_inv_id e
  inv_hom_id := sourceKIso_inv_hom_id e

section PropertyP

variable {S S' : DifferentialGradedBimodule.{u, w, x, y} A B}

/-- Tensoring a property-P right DG `A`-module with a bimodule quasi-isomorphism produces a
quasi-isomorphism of right DG `B`-modules. -/
@[stacks 09LT "property-P tensoring preserves bimodule quasi-isomorphisms"]
theorem mapBimodule_quasiIso_of_hasPropertyP (f : S ⟶ S')
    (hf : DifferentialGradedBimodule.quasiIso A B f)
    {M : DifferentialGradedModule.{u, x} A}
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map (mapBimodule M f)) := sorry

/-- On a property-P representative, the homotopy tensor transformation induced by a bimodule
quasi-isomorphism belongs to the target quasi-isomorphism class. -/
@[stacks 09LT "property-P homotopy tensor comparison is a quasi-isomorphism"]
theorem sourceK_app_quasiIso_of_hasPropertyP (f : S ⟶ S')
    (hf : DifferentialGradedBimodule.quasiIso A B f)
    {M : DifferentialGradedModule.{u, x} A}
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    DifferentialGradedModule.quasiIso B
      ((sourceK f).app ((DifferentialGradedModule.toK A).obj M)) := sorry

end PropertyP

#synth (Closed.bimoduleFunctor (A := A) (B := B)).Additive
#synth Functor.Linear R (Closed.bimoduleFunctor (A := A) (B := B))
#synth (Homotopy.bimoduleFunctor (A := A) (B := B)).Additive
#synth Functor.Linear R (Homotopy.bimoduleFunctor (A := A) (B := B))

end DifferentialGradedBimodule.Tensor
