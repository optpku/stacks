/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Naturality
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Naturality of the Differential Graded Tensor-Hom Equivalence

The degreewise tensor-Hom equivalence and its Hom-complex isomorphism are contravariantly natural
in the tensor source and bimodule variables and covariantly natural in the target.  The statements
use the shared enriched Hom-complex precomposition and postcomposition maps, so downstream
constructions can rewrite whole cochain maps without unfolding currying representatives.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory
open DifferentialGradedModule
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.TensorHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}
variable {N N' : DifferentialGradedBimodule.{u, v, w, x} A B}
variable {M M' : DifferentialGradedModule.{u, v} A}
variable {P P' : DifferentialGradedModule.{u, v} B}

/-- Tensor-Hom currying is enriched-natural in an arbitrary homogeneous map of first
arguments. -/
@[stacks 09LN "enriched left naturality of DG tensor-Hom currying"]
theorem homEquiv_natural_left {i k : ℤ} (f : GradedHom A M' M i)
    (g : GradedHom B (Tensor.obj M N) P k) :
    homEquiv N M' P (i + k) (gradedHomComp g (Tensor.map N f)) =
      gradedHomComp (homEquiv N M P k g) f := sorry

/-- Tensor-Hom currying is degreewise natural in the DG bimodule argument. -/
@[stacks 09LN "enriched middle naturality of DG tensor-Hom currying"]
theorem homEquiv_natural_middle (f : N ⟶ N') (k : ℤ)
    (g : GradedHom B (Tensor.obj M N') P k) :
    homEquiv N M P k
        (HomComplex.precompLinear (homToCompHom (Tensor.mapBimodule M f)) k g) =
      HomComplex.postcompLinear (homToCompHom (InternalHom.precomp f P)) k
        (homEquiv N' M P k g) := sorry

/-- Tensor-Hom currying is enriched-natural in an arbitrary homogeneous target map. -/
@[stacks 09LN "enriched target naturality of DG tensor-Hom currying"]
theorem homEquiv_natural_target {j k : ℤ} (f : GradedHom B P P' j)
    (g : GradedHom B (Tensor.obj M N) P k) :
    homEquiv N M P' (k + j) (gradedHomComp f g) =
      gradedHomComp (internalHomMap N f) (homEquiv N M P k g) := sorry

/-- Tensor-Hom uncurrying is enriched-natural in an arbitrary homogeneous map of first
arguments. -/
@[stacks 09LN "enriched left naturality of DG tensor-Hom uncurrying"]
theorem homEquiv_symm_natural_left {i k : ℤ} (f : GradedHom A M' M i)
    (g : GradedHom A M (internalHom N P) k) :
    (homEquiv N M' P (i + k)).symm (gradedHomComp g f) =
      gradedHomComp ((homEquiv N M P k).symm g) (Tensor.map N f) := sorry

/-- Tensor-Hom uncurrying is degreewise natural in the DG bimodule argument. -/
@[stacks 09LN "enriched middle naturality of DG tensor-Hom uncurrying"]
theorem homEquiv_symm_natural_middle (f : N ⟶ N') (k : ℤ)
    (g : GradedHom A M (internalHom N' P) k) :
    (homEquiv N M P k).symm
        (HomComplex.postcompLinear (homToCompHom (InternalHom.precomp f P)) k g) =
      HomComplex.precompLinear (homToCompHom (Tensor.mapBimodule M f)) k
        ((homEquiv N' M P k).symm g) := sorry

/-- Tensor-Hom uncurrying is enriched-natural in an arbitrary homogeneous target map. -/
@[stacks 09LN "enriched target naturality of DG tensor-Hom uncurrying"]
theorem homEquiv_symm_natural_target {j k : ℤ} (f : GradedHom B P P' j)
    (g : GradedHom A M (internalHom N P) k) :
    (homEquiv N M P' (k + j)).symm
        (gradedHomComp (internalHomMap N f) g) =
      gradedHomComp f ((homEquiv N M P k).symm g) := sorry

/-- The Hom-complex tensor-Hom isomorphism is contravariantly natural in the first DG module. -/
@[stacks 09LN "DG tensor-Hom naturality in the first module"]
theorem homComplexIso_natural_left (f : CompHom M' M) :
    HomComplex.precomp ((Tensor.dgFunctor N).mapCompHom f) ≫
        (homComplexIso N M' P).hom =
      (homComplexIso N M P).hom ≫
        HomComplex.precomp f := sorry

/-- The Hom-complex tensor-Hom isomorphism is contravariantly natural in the DG bimodule. -/
@[stacks 09LN "DG tensor-Hom naturality in the bimodule"]
theorem homComplexIso_natural_middle (f : N ⟶ N') :
    HomComplex.precomp (homToCompHom (Tensor.mapBimodule M f)) ≫
        (homComplexIso N M P).hom =
      (homComplexIso N' M P).hom ≫
        HomComplex.postcomp (homToCompHom (InternalHom.precomp f P)) := sorry

/-- The Hom-complex tensor-Hom isomorphism is covariantly natural in the target DG module. -/
@[stacks 09LN "DG tensor-Hom naturality in the target module"]
theorem homComplexIso_natural_target (f : CompHom P P') :
    HomComplex.postcomp f ≫
        (homComplexIso N M P').hom =
      (homComplexIso N M P).hom ≫
        HomComplex.postcomp ((internalHomDgFunctor N).mapCompHom f) := sorry

/-- The inverse Hom-complex tensor-Hom isomorphism is contravariantly natural in the first DG
module. -/
@[stacks 09LN "inverse DG tensor-Hom naturality in the first module"]
theorem homComplexIso_inv_natural_left (f : CompHom M' M) :
    HomComplex.precomp f ≫ (homComplexIso N M' P).inv =
      (homComplexIso N M P).inv ≫
        HomComplex.precomp ((Tensor.dgFunctor N).mapCompHom f) := sorry

/-- The inverse Hom-complex tensor-Hom isomorphism is contravariantly natural in the DG
bimodule. -/
@[stacks 09LN "inverse DG tensor-Hom naturality in the bimodule"]
theorem homComplexIso_inv_natural_middle (f : N ⟶ N') :
    HomComplex.postcomp (homToCompHom (InternalHom.precomp f P)) ≫
        (homComplexIso N M P).inv =
      (homComplexIso N' M P).inv ≫
        HomComplex.precomp (homToCompHom (Tensor.mapBimodule M f)) := sorry

/-- The inverse Hom-complex tensor-Hom isomorphism is covariantly natural in the target DG
module. -/
@[stacks 09LN "inverse DG tensor-Hom naturality in the target module"]
theorem homComplexIso_inv_natural_target (f : CompHom P P') :
    HomComplex.postcomp ((internalHomDgFunctor N).mapCompHom f) ≫
        (homComplexIso N M P').inv =
      (homComplexIso N M P).inv ≫ HomComplex.postcomp f := sorry

namespace HomComplex

/-- The Hom-complex bifunctor after tensoring its contravariant argument with a fixed DG
bimodule. -/
@[stacks 09LN "source Hom-complex bifunctor for DG tensor-Hom"]
def source (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Comp R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
        Comp R (DifferentialGradedModule.{u, v} B) ⥤
      CochainComplex (ModuleCat.{v} R) ℤ :=
  ((Tensor.dgFunctor N).mapComp.op.prod (𝟭 _)) ⋙
    DifferentialGradedCategory.HomComplex.bifunctor

/-- The Hom-complex bifunctor after applying fixed-source internal Hom to its covariant
argument. -/
@[stacks 09LN "target Hom-complex bifunctor for DG tensor-Hom"]
def target (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Comp R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
        Comp R (DifferentialGradedModule.{u, v} B) ⥤
      CochainComplex (ModuleCat.{v} R) ℤ :=
  ((𝟭 _).prod (internalHomDgFunctor N).mapComp) ⋙
    DifferentialGradedCategory.HomComplex.bifunctor

/-- The componentwise Hom-complex tensor-Hom isomorphisms are natural in both module
arguments. -/
@[stacks 09LN "naturality of the DG tensor-Hom bifunctor isomorphism"]
theorem iso_naturality (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {X Y : (Comp R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
      Comp R (DifferentialGradedModule.{u, v} B)} (f : X ⟶ Y) :
    (source N).map f ≫ (homComplexIso N Y.1.unop.obj Y.2.obj).hom =
      (homComplexIso N X.1.unop.obj X.2.obj).hom ≫ (target N).map f := sorry

/-- The inverse componentwise Hom-complex tensor-Hom isomorphisms are natural in both module
arguments. -/
@[stacks 09LN "inverse naturality of the DG tensor-Hom bifunctor isomorphism"]
theorem iso_inv_naturality (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {X Y : (Comp R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
      Comp R (DifferentialGradedModule.{u, v} B)} (f : X ⟶ Y) :
    (target N).map f ≫ (homComplexIso N Y.1.unop.obj Y.2.obj).inv =
      (homComplexIso N X.1.unop.obj X.2.obj).inv ≫ (source N).map f := sorry

/-- The DG tensor-Hom isomorphism as a natural isomorphism of enriched Hom-complex
bifunctors. -/
@[stacks 09LN "natural isomorphism of DG tensor-Hom bifunctors"]
noncomputable def iso (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    source N ≅ target N :=
  NatIso.ofComponents
    (fun X ↦ homComplexIso N X.1.unop.obj X.2.obj)
    (fun f ↦ iso_naturality N f)

/-- The forward component of the enriched tensor-Hom natural isomorphism is currying. -/
@[simp, stacks 09LN "forward component of the DG tensor-Hom bifunctor isomorphism"]
theorem iso_hom_app (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (X : (Comp R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
      Comp R (DifferentialGradedModule.{u, v} B)) :
    (iso N).hom.app X = homComplexForward N X.1.unop.obj X.2.obj := sorry

/-- The inverse component of the enriched tensor-Hom natural isomorphism is uncurrying. -/
@[simp, stacks 09LN "inverse component of the DG tensor-Hom bifunctor isomorphism"]
theorem iso_inv_app (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (X : (Comp R (DifferentialGradedModule.{u, v} A))ᵒᵖ ×
      Comp R (DifferentialGradedModule.{u, v} B)) :
    (iso N).inv.app X = homComplexBackward N X.1.unop.obj X.2.obj := sorry

end HomComplex

/-- Closed linear tensor-Hom currying is natural in the first DG module. -/
@[stacks 09LN "left naturality of closed linear tensor-Hom currying"]
theorem compHomLinearEquiv_natural_left
    {X X' : Comp R (DifferentialGradedModule.{u, v} A)}
    {Y : Comp R (DifferentialGradedModule.{u, v} B)}
    (f : X' ⟶ X) (g : (Tensor.dgFunctor N).mapComp.obj X ⟶ Y) :
    compHomLinearEquiv N X' Y ((Tensor.dgFunctor N).mapComp.map f ≫ g) =
      f ≫ compHomLinearEquiv N X Y g := sorry

/-- Closed linear tensor-Hom currying is natural in the DG bimodule. -/
@[stacks 09LN "middle naturality of closed linear tensor-Hom currying"]
theorem compHomLinearEquiv_natural_middle (f : N ⟶ N')
    (X : Comp R (DifferentialGradedModule.{u, v} A))
    (Y : Comp R (DifferentialGradedModule.{u, v} B))
    (g : (Tensor.dgFunctor N').mapComp.obj X ⟶ Y) :
    compHomLinearEquiv N X Y ((Tensor.sourceComp f).app X ≫ g) =
      compHomLinearEquiv N' X Y g ≫ (InternalHom.precompComp f).app Y := sorry

/-- Closed linear tensor-Hom uncurrying is natural in the DG bimodule. -/
@[stacks 09LN "middle naturality of closed linear tensor-Hom uncurrying"]
theorem compHomLinearEquiv_symm_natural_middle (f : N ⟶ N')
    (X : Comp R (DifferentialGradedModule.{u, v} A))
    (Y : Comp R (DifferentialGradedModule.{u, v} B))
    (g : X ⟶ (internalHomDgFunctor N').mapComp.obj Y) :
    (compHomLinearEquiv N X Y).symm (g ≫ (InternalHom.precompComp f).app Y) =
      (Tensor.sourceComp f).app X ≫ (compHomLinearEquiv N' X Y).symm g := sorry

namespace Closed

/-- Closed precomposition on internal Hom is the mate of the corresponding closed tensor
transformation in the DG bimodule parameter. -/
@[stacks 09LN "mate compatibility of closed DG tensor and internal Hom"]
theorem precomp_eq_conjugateEquiv (f : N ⟶ N') :
    InternalHom.precompComp f =
      conjugateEquiv (adjunction N') (adjunction N) (Tensor.sourceComp f) := sorry

/-- Closed tensor-Hom currying is natural in the differential graded bimodule parameter, expressed
through the bundled parameter functors. -/
@[stacks 09LN "parameter naturality of the closed DG tensor-Hom equivalence"]
theorem homEquiv_naturality_parameter {N N' : DifferentialGradedBimodule.{u, v, w, x} A B}
    (f : N ⟶ N')
    {M : Comp R (DifferentialGradedModule.{u, v} A)}
    {P : Comp R (DifferentialGradedModule.{u, v} B)}
    (g : ((Tensor.Closed.bimoduleFunctor (A := A) (B := B)).obj N').obj M ⟶ P) :
    (adjunction N).homEquiv M P
        (((Tensor.Closed.bimoduleFunctor (A := A) (B := B)).map f).app M ≫ g) =
      (adjunction N').homEquiv M P g ≫
        ((InternalHom.Closed.bimoduleFunctor (A := A) (B := B)).map f.op).app P := sorry

/-- Closed relative tensor and internal Hom form an adjunction parametrized by the differential
graded bimodule. -/
@[stacks 09LN "parametrized closed DG tensor-Hom adjunction"]
def parametrizedAdjunction :
    Tensor.Closed.bimoduleFunctor.{u, v, v, w, x} (A := A) (B := B) ⊣₂
      InternalHom.Closed.bimoduleFunctor.{u, v, w, x} (A := A) (B := B) :=
  ParametrizedAdjunction.mk'
    (fun N ↦ adjunction N)
    (fun {N N'} f {M} {P} g ↦
      homEquiv_naturality_parameter (N := N) (N' := N') f (M := M) (P := P) g)

/-- The closed parametrized adjunction specializes to the fixed-bimodule tensor-Hom adjunction. -/
@[simp, stacks 09LN "closed parametrized DG tensor-Hom adjunction at a bimodule"]
theorem parametrizedAdjunction_adj (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (parametrizedAdjunction (A := A) (B := B)).adj N = adjunction N := sorry

end Closed

/-- Closed linear tensor-Hom currying is natural in the target DG module. -/
@[stacks 09LN "target naturality of closed linear tensor-Hom currying"]
theorem compHomLinearEquiv_natural_target
    (X : Comp R (DifferentialGradedModule.{u, v} A))
    {Y Y' : Comp R (DifferentialGradedModule.{u, v} B)}
    (f : Y ⟶ Y') (g : (Tensor.dgFunctor N).mapComp.obj X ⟶ Y) :
    compHomLinearEquiv N X Y' (g ≫ f) =
      compHomLinearEquiv N X Y g ≫
        (internalHomDgFunctor N).mapComp.map f := sorry

/-- Homotopy-category linear tensor-Hom currying is natural in the first DG module. -/
@[stacks 09LT "left naturality of homotopy linear tensor-Hom currying"]
theorem homotopyHomLinearEquiv_natural_left
    {X X' : K R (DifferentialGradedModule.{u, v} A)}
    {Y : K R (DifferentialGradedModule.{u, v} B)}
    (f : X' ⟶ X) (g : (Tensor.dgFunctor N).mapK.obj X ⟶ Y) :
    homotopyHomLinearEquiv N X' Y ((Tensor.dgFunctor N).mapK.map f ≫ g) =
      f ≫ homotopyHomLinearEquiv N X Y g := sorry

/-- Homotopy-category linear tensor-Hom currying is natural in the DG bimodule. -/
@[stacks 09LT "middle naturality of homotopy linear tensor-Hom currying"]
theorem homotopyHomLinearEquiv_natural_middle (f : N ⟶ N')
    (X : K R (DifferentialGradedModule.{u, v} A))
    (Y : K R (DifferentialGradedModule.{u, v} B))
    (g : (Tensor.dgFunctor N').mapK.obj X ⟶ Y) :
    homotopyHomLinearEquiv N X Y ((Tensor.sourceK f).app X ≫ g) =
      homotopyHomLinearEquiv N' X Y g ≫ (InternalHom.precompK f).app Y := sorry

/-- Homotopy-category linear tensor-Hom uncurrying is natural in the DG bimodule. -/
@[stacks 09LT "middle naturality of homotopy linear tensor-Hom uncurrying"]
theorem homotopyHomLinearEquiv_symm_natural_middle (f : N ⟶ N')
    (X : K R (DifferentialGradedModule.{u, v} A))
    (Y : K R (DifferentialGradedModule.{u, v} B))
    (g : X ⟶ (internalHomDgFunctor N').mapK.obj Y) :
    (homotopyHomLinearEquiv N X Y).symm (g ≫ (InternalHom.precompK f).app Y) =
      (Tensor.sourceK f).app X ≫ (homotopyHomLinearEquiv N' X Y).symm g := sorry

namespace Homotopy

/-- Homotopy-category precomposition on internal Hom is the mate of the corresponding tensor
transformation in the DG bimodule parameter. -/
@[stacks 09LT "mate compatibility of homotopy DG tensor and internal Hom"]
theorem precomp_eq_conjugateEquiv (f : N ⟶ N') :
    InternalHom.precompK f =
      conjugateEquiv (homotopyAdjunction N') (homotopyAdjunction N)
        (Tensor.sourceK f) := sorry

set_option maxHeartbeats 400000 in
/-- Homotopy tensor-Hom currying is natural in the differential graded bimodule parameter,
expressed through the bundled parameter functors. -/
@[stacks 09LT "parameter naturality of the homotopy DG tensor-Hom equivalence"]
theorem homEquiv_naturality_parameter {N N' : DifferentialGradedBimodule.{u, v, w, x} A B}
    (f : N ⟶ N')
    {M : K R (DifferentialGradedModule.{u, v} A)}
    {P : K R (DifferentialGradedModule.{u, v} B)}
    (g : ((Tensor.Homotopy.bimoduleFunctor (A := A) (B := B)).obj N').obj M ⟶ P) :
    (homotopyAdjunction N).homEquiv M P
        (((Tensor.Homotopy.bimoduleFunctor (A := A) (B := B)).map f).app M ≫ g) =
      (homotopyAdjunction N').homEquiv M P g ≫
        ((InternalHom.Homotopy.bimoduleFunctor (A := A) (B := B)).map f.op).app P := sorry

/-- Homotopy relative tensor and internal Hom form an adjunction parametrized by the differential
graded bimodule. -/
@[stacks 09LT "parametrized homotopy DG tensor-Hom adjunction"]
def parametrizedAdjunction :
    Tensor.Homotopy.bimoduleFunctor.{u, v, v, w, x} (A := A) (B := B) ⊣₂
      InternalHom.Homotopy.bimoduleFunctor.{u, v, w, x} (A := A) (B := B) :=
  ParametrizedAdjunction.mk'
    (fun N ↦ homotopyAdjunction N)
    (fun {N N'} f {M} {P} g ↦
      homEquiv_naturality_parameter (N := N) (N' := N') f (M := M) (P := P) g)

/-- The homotopy parametrized adjunction specializes to the fixed-bimodule tensor-Hom
adjunction. -/
@[simp, stacks 09LT "homotopy parametrized DG tensor-Hom adjunction at a bimodule"]
theorem parametrizedAdjunction_adj (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (parametrizedAdjunction (A := A) (B := B)).adj N = homotopyAdjunction N := sorry

end Homotopy

/-- Homotopy-category linear tensor-Hom currying is natural in the target DG module. -/
@[stacks 09LT "target naturality of homotopy linear tensor-Hom currying"]
theorem homotopyHomLinearEquiv_natural_target
    (X : K R (DifferentialGradedModule.{u, v} A))
    {Y Y' : K R (DifferentialGradedModule.{u, v} B)}
    (f : Y ⟶ Y') (g : (Tensor.dgFunctor N).mapK.obj X ⟶ Y) :
    homotopyHomLinearEquiv N X Y' (g ≫ f) =
      homotopyHomLinearEquiv N X Y g ≫
        (internalHomDgFunctor N).mapK.map f := sorry

/-- The DG tensor-Hom isomorphism induces an isomorphism on every degree of Hom-complex
cohomology. -/
@[stacks 09LN "DG tensor-Hom isomorphism on Hom-complex cohomology"]
noncomputable def homologyIso (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (homComplex (Tensor.obj M N) P).homology k ≅
      (homComplex M (internalHom N P)).homology k :=
  HomologicalComplex.homologyMapIso (homComplexIso N M P) k

/-- The homology tensor-Hom isomorphism computes by the forward Hom-complex map. -/
@[simp, stacks 09LN "forward map of the homology tensor-Hom isomorphism"]
theorem homologyIso_hom (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (homologyIso N M P k).hom =
      HomologicalComplex.homologyMap (homComplexIso N M P).hom k := sorry

/-- The inverse homology tensor-Hom isomorphism computes by the inverse Hom-complex map. -/
@[simp, stacks 09LN "inverse map of the homology tensor-Hom isomorphism"]
theorem homologyIso_inv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (homologyIso N M P k).inv =
      HomologicalComplex.homologyMap (homComplexIso N M P).inv k := sorry

/-- Homology tensor-Hom currying is natural in the first DG module. -/
@[stacks 09LN "left naturality of homology tensor-Hom currying"]
theorem homologyIso_natural_left (f : CompHom M' M) (k : ℤ) :
    HomologicalComplex.homologyMap
          (HomComplex.precomp ((Tensor.dgFunctor N).mapCompHom f)) k ≫
        (homologyIso N M' P k).hom =
      (homologyIso N M P k).hom ≫
        HomologicalComplex.homologyMap (HomComplex.precomp f) k := sorry

/-- Homology tensor-Hom currying is natural in the DG bimodule. -/
@[stacks 09LN "middle naturality of homology tensor-Hom currying"]
theorem homologyIso_natural_middle (f : N ⟶ N') (k : ℤ) :
    HomologicalComplex.homologyMap
          (HomComplex.precomp (homToCompHom (Tensor.mapBimodule M f))) k ≫
        (homologyIso N M P k).hom =
      (homologyIso N' M P k).hom ≫
        HomologicalComplex.homologyMap
          (HomComplex.postcomp (homToCompHom (InternalHom.precomp f P))) k := sorry

/-- Homology tensor-Hom currying is natural in the target DG module. -/
@[stacks 09LN "target naturality of homology tensor-Hom currying"]
theorem homologyIso_natural_target (f : CompHom P P') (k : ℤ) :
    HomologicalComplex.homologyMap (HomComplex.postcomp f) k ≫
        (homologyIso N M P' k).hom =
      (homologyIso N M P k).hom ≫
        HomologicalComplex.homologyMap
          (HomComplex.postcomp ((internalHomDgFunctor N).mapCompHom f)) k := sorry

/-- Inverse homology tensor-Hom currying is natural in the first DG module. -/
@[stacks 09LN "left naturality of inverse homology tensor-Hom currying"]
theorem homologyIso_inv_natural_left (f : CompHom M' M) (k : ℤ) :
    HomologicalComplex.homologyMap (HomComplex.precomp f) k ≫
        (homologyIso N M' P k).inv =
      (homologyIso N M P k).inv ≫
        HomologicalComplex.homologyMap
          (HomComplex.precomp ((Tensor.dgFunctor N).mapCompHom f)) k := sorry

/-- Inverse homology tensor-Hom currying is natural in the DG bimodule. -/
@[stacks 09LN "middle naturality of inverse homology tensor-Hom currying"]
theorem homologyIso_inv_natural_middle (f : N ⟶ N') (k : ℤ) :
    HomologicalComplex.homologyMap
          (HomComplex.postcomp (homToCompHom (InternalHom.precomp f P))) k ≫
        (homologyIso N M P k).inv =
      (homologyIso N' M P k).inv ≫
        HomologicalComplex.homologyMap
          (HomComplex.precomp (homToCompHom (Tensor.mapBimodule M f))) k := sorry

/-- Inverse homology tensor-Hom currying is natural in the target DG module. -/
@[stacks 09LN "target naturality of inverse homology tensor-Hom currying"]
theorem homologyIso_inv_natural_target (f : CompHom P P') (k : ℤ) :
    HomologicalComplex.homologyMap
          (HomComplex.postcomp ((internalHomDgFunctor N).mapCompHom f)) k ≫
        (homologyIso N M P' k).inv =
      (homologyIso N M P k).inv ≫
        HomologicalComplex.homologyMap (HomComplex.postcomp f) k := sorry

end DifferentialGradedBimodule.TensorHom
