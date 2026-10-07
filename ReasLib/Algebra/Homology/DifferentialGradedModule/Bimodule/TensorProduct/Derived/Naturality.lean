module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Transformation
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Linear.Left

/-!
# Naturality of derived tensor product in the bimodule variable

The explicit transformation `sourceK f` induces the canonical transformation between total
left-derived tensor functors. A bimodule quasi-isomorphism is invertible on property-P tensor
models and hence induces an isomorphism of derived functors.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory DifferentialGradedCategory

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable {N N' N'' : DifferentialGradedBimodule.{u, w, x, y} A B}

/-- The map between homotopy-level sources of derived tensor product induced covariantly by a
bimodule morphism. -/
@[stacks 09S3 "derived tensor source map in the bimodule variable"]
def derivedSourceMap (f : N ⟶ N') :
    derivedSourceFunctor.{u, v, w, x, y} N ⟶ derivedSourceFunctor.{u, v, w, x, y} N' :=
  Functor.whiskerRight (sourceK.{u, v, w, x, y} f)
    (DifferentialGradedModule.Derived.Q.{u, max v w, y} B)

/-- A component of the derived tensor source map is localization of the explicit homotopy
tensor map. -/
@[simp, stacks 09S3 "component of the derived tensor source map"]
theorem derivedSourceMap_app (f : N ⟶ N')
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (derivedSourceMap f).app M =
      (DifferentialGradedModule.Derived.Q.{u, max v w, y} B).map
        ((sourceK.{u, v, w, x, y} f).app M) := sorry

/-- The identity bimodule morphism induces the identity map between derived tensor sources. -/
@[simp, stacks 09S3 "identity law for derived tensor source maps"]
theorem derivedSourceMap_id (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    derivedSourceMap (𝟙 N) = 𝟙 (derivedSourceFunctor.{u, v, w, x, y} N) := sorry

/-- Maps between derived tensor sources preserve composition of bimodule morphisms. -/
@[simp, stacks 09S3 "composition law for derived tensor source maps"]
theorem derivedSourceMap_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    derivedSourceMap (f ≫ g) = derivedSourceMap f ≫ derivedSourceMap g := sorry

/-- The zero bimodule morphism induces the zero map between derived tensor sources. -/
@[simp]
theorem derivedSourceMap_zero
    (N N' : DifferentialGradedBimodule.{u, w, x, y} A B) :
    derivedSourceMap (0 : N ⟶ N') = 0 := sorry

/-- Maps between derived tensor sources are additive in the bimodule morphism. -/
@[simp]
theorem derivedSourceMap_add (f g : N ⟶ N') :
    derivedSourceMap (f + g) = derivedSourceMap f + derivedSourceMap g := sorry

/-- Maps between derived tensor sources are `R`-linear in the bimodule morphism. -/
@[simp]
theorem derivedSourceMap_smul (r : R) (f : N ⟶ N') :
    derivedSourceMap (r • f) = r • derivedSourceMap f := sorry

/-- A bimodule isomorphism induces the explicit isomorphism between the homotopy-level sources
of the two derived tensor functors. -/
@[stacks 09S3 "derived tensor source isomorphism"]
def derivedSourceIso (e : N ≅ N') :
    derivedSourceFunctor.{u, v, w, x, y} N ≅ derivedSourceFunctor.{u, v, w, x, y} N' :=
  Functor.isoWhiskerRight (sourceKIso.{u, v, w, x, y} e)
    (DifferentialGradedModule.Derived.Q.{u, max v w, y} B)

/-- The forward map of the derived tensor source isomorphism is induced by the forward
bimodule map. -/
@[simp, stacks 09S3 "forward derived tensor source isomorphism"]
theorem derivedSourceIso_hom (e : N ≅ N') :
    (derivedSourceIso e).hom = derivedSourceMap e.hom := sorry

/-- The inverse of the source isomorphism is induced by the inverse bimodule morphism. -/
@[simp, stacks 09S3 "inverse derived tensor source isomorphism"]
theorem derivedSourceIso_inv (e : N ≅ N') :
    (derivedSourceIso e).inv = derivedSourceMap e.inv := sorry

/-- Lemma 22.33.3 (09S3) (1): a bimodule morphism induces the canonical covariant natural
transformation between total left-derived tensor functors. -/
@[stacks 09S3 "naturality of derived tensor in the bimodule variable"]
noncomputable def derivedNatTrans (f : N ⟶ N') :
    derivedFunctor.{u, v, w, x, y} N ⟶ derivedFunctor.{u, v, w, x, y} N' :=
  Functor.LeftDerived.mapNatTrans (DifferentialGradedModule.Derived.Q.{u, v, x} A)
    (DifferentialGradedModule.quasiIso.{u, v, x} A) (derivedSourceMap f)

/-- The derived tensor transformation is characterized by the universal comparison square with
the explicit homotopy-level tensor transformation. -/
@[reassoc (attr := simp), stacks 09S3 "derived tensor naturality comparison square"]
theorem derivedNatTrans_fac (f : N ⟶ N') :
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q.{u, v, x} A)
        (derivedNatTrans f) ≫
        derivedCounit.{u, v, w, x, y} N' =
      derivedCounit.{u, v, w, x, y} N ≫ derivedSourceMap f := sorry

/-- The identity bimodule morphism induces the identity derived tensor transformation. -/
@[simp, stacks 09S3 "identity law for derived tensor transformations"]
theorem derivedNatTrans_id (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    derivedNatTrans (𝟙 N) = 𝟙 (derivedFunctor.{u, v, w, x, y} N) := sorry

/-- Derived tensor transformations preserve composition of bimodule morphisms. -/
@[simp, stacks 09S3 "composition law for derived tensor transformations"]
theorem derivedNatTrans_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    derivedNatTrans (f ≫ g) = derivedNatTrans f ≫ derivedNatTrans g := sorry

/-- The zero bimodule morphism induces the zero derived tensor transformation. -/
@[simp]
theorem derivedNatTrans_zero
    (N N' : DifferentialGradedBimodule.{u, w, x, y} A B) :
    derivedNatTrans (0 : N ⟶ N') = 0 := sorry

/-- Derived tensor transformations are additive in the bimodule morphism. -/
@[simp]
theorem derivedNatTrans_add (f g : N ⟶ N') :
    derivedNatTrans (f + g) = derivedNatTrans f + derivedNatTrans g := sorry

/-- Derived tensor transformations are `R`-linear in the bimodule morphism. -/
@[simp]
theorem derivedNatTrans_smul (r : R) (f : N ⟶ N') :
    derivedNatTrans (r • f) = r • derivedNatTrans f := sorry

/-- Total derived tensor is a functor covariant in its bimodule parameter. -/
@[stacks 09S3 "derived tensor as a functor of the bimodule"]
noncomputable def derivedBimoduleFunctor (A : CochainDGAlgebra.{u, x} R)
    (B : CochainDGAlgebra.{u, y} R) :
    DifferentialGradedBimodule.{u, w, x, y} A B ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} A ⥤
        DifferentialGradedModule.Derived.Category.{u, max v w} B) where
  obj N := derivedFunctor.{u, v, w, x, y} N
  map f := derivedNatTrans f
  map_id := sorry
  map_comp := sorry

/-- Evaluating the derived tensor parameter functor gives tensoring by the fixed bimodule. -/
@[simp, stacks 09S3 "object formula for the derived tensor parameter functor"]
theorem derivedBimoduleFunctor_obj (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedBimoduleFunctor A B).obj N = derivedFunctor.{u, v, w, x, y} N := sorry

/-- The derived tensor parameter functor maps a bimodule morphism by its canonical derived
transformation. -/
@[simp, stacks 09S3 "map formula for the derived tensor parameter functor"]
theorem derivedBimoduleFunctor_map
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f : N ⟶ N') :
    (derivedBimoduleFunctor A B).map f = derivedNatTrans f := sorry

/-- The derived tensor parameter functor is additive. -/
@[stacks 09S3 "additive derived tensor parameter functor"]
instance derivedBimoduleFunctorAdditive :
    (derivedBimoduleFunctor A B).Additive := sorry

/-- The derived tensor parameter functor is `R`-linear. -/
@[stacks 09S3 "linear derived tensor parameter functor"]
instance derivedBimoduleFunctorLinear :
    Functor.Linear R (derivedBimoduleFunctor A B) := sorry

/-- A strict bimodule isomorphism induces a natural isomorphism between total left-derived
tensor functors. -/
@[stacks 09S3 "derived tensor natural isomorphism in the bimodule variable"]
noncomputable def derivedNatIso (e : N ≅ N') :
    derivedFunctor N ≅ derivedFunctor N' :=
  Functor.LeftDerived.mapNatIso (DifferentialGradedModule.Derived.Q.{u, v, x} A)
    (DifferentialGradedModule.quasiIso.{u, v, x} A) (derivedSourceIso e)

/-- The forward map of the derived tensor isomorphism is the canonical transformation induced
by the forward bimodule morphism. -/
@[simp, stacks 09S3 "forward derived tensor natural isomorphism"]
theorem derivedNatIso_hom (e : N ≅ N') :
    (derivedNatIso e).hom = derivedNatTrans e.hom := sorry

/-- The inverse of the derived tensor isomorphism is induced by the inverse bimodule map. -/
@[simp, stacks 09S3 "inverse derived tensor natural isomorphism"]
theorem derivedNatIso_inv (e : N ≅ N') :
    (derivedNatIso e).inv = derivedNatTrans e.inv := sorry

section PropertyP

variable {A₀ : CochainDGAlgebra.{u, v} R}
variable {S S' : DifferentialGradedBimodule.{u, w, v, y} A₀ B}

/-- On a property-P representative, a bimodule quasi-isomorphism gives an isomorphism between
the localized underived tensor values. -/
@[stacks 09S3 "property-P derived tensor source isomorphism"]
theorem derivedSourceMap_app_isIso_of_hasPropertyP (f : S ⟶ S')
    (hf : DifferentialGradedBimodule.quasiIso A₀ B f)
    {M : DifferentialGradedModule.{u, v} A₀}
    (hM : DifferentialGradedModule.HasPropertyP A₀ M) :
    IsIso ((derivedSourceMap f).app ((DifferentialGradedModule.toK A₀).obj M)) := sorry

/-- At the derived image of a property-P representative, the derived tensor transformation of
a bimodule quasi-isomorphism is an isomorphism. -/
@[stacks 09S3 "property-P derived tensor transformation isomorphism"]
theorem derivedNatTrans_app_isIso_of_hasPropertyP (f : S ⟶ S')
    (hf : DifferentialGradedBimodule.quasiIso A₀ B f)
    {M : DifferentialGradedModule.{u, v} A₀}
    (hM : DifferentialGradedModule.HasPropertyP A₀ M) :
    IsIso ((derivedNatTrans f).app
      ((DifferentialGradedModule.Derived.Q A₀).obj
        ((DifferentialGradedModule.toK A₀).obj M))) := sorry

end PropertyP

/-- Lemma 22.33.3 (09S3) (2): a bimodule quasi-isomorphism induces an isomorphism between
the corresponding total left-derived tensor functors. -/
@[stacks 09S3 "derived tensor inverts bimodule quasi-isomorphisms",
  stacks 0FTJ "quasi-isomorphic bimodules induce isomorphic derived tensor functors"]
theorem derivedNatTrans_isIso_of_quasiIso (f : N ⟶ N')
    (hf : DifferentialGradedBimodule.quasiIso A B f) :
    IsIso (derivedNatTrans f) := sorry

/-- The derived tensor parameter functor inverts all bimodule quasi-isomorphisms. -/
@[stacks 09S3 "derived tensor descends along bimodule quasi-isomorphisms"]
theorem derivedBimoduleFunctor_inverts (A : CochainDGAlgebra.{u, x} R)
    (B : CochainDGAlgebra.{u, y} R) :
    (DifferentialGradedBimodule.quasiIso A B).IsInvertedBy
      (derivedBimoduleFunctor A B) := sorry

#synth (derivedBimoduleFunctor A B).Additive
#synth Functor.Linear R (derivedBimoduleFunctor A B)

end DifferentialGradedBimodule.Tensor
