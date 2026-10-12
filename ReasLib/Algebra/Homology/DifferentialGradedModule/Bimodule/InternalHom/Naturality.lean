/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.CategoryTheory.Linear.Opposite
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Naturality of Fixed-Source Internal Hom

A morphism of differential graded bimodules acts on fixed-source internal Hom by
precomposition, while a morphism of target modules acts by postcomposition. This file exposes
both concrete maps before passing to the closed and homotopy categories, so downstream derived
constructions do not need to rebuild representatives.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}
variable {T T' T'' : DifferentialGradedBimodule.{u, v, w, x} A B}

/-- A morphism of target right DG `B`-modules acts covariantly on fixed-source internal Hom by
postcomposition. -/
@[stacks 09LN "postcomposition on fixed-source DG internal Hom"]
def postcomp (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    {P Q : DifferentialGradedModule.{u, v} B} (g : P ⟶ Q) :
    DifferentialGradedBimodule.internalHom T P ⟶
      DifferentialGradedBimodule.internalHom T Q :=
  DifferentialGradedModule.compHomToHom
    (DifferentialGradedBimodule.internalHomMapClosed T
      (DifferentialGradedModule.homToCompHom g))

/-- Postcomposition by an identity map is the identity on fixed-source internal Hom. -/
@[simp]
theorem postcomp_id (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : DifferentialGradedModule.{u, v} B) :
    postcomp T (𝟙 P) = 𝟙 (DifferentialGradedBimodule.internalHom T P) := sorry

/-- Fixed-source internal Hom preserves composition of target maps. -/
@[simp]
theorem postcomp_comp (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    {P Q U : DifferentialGradedModule.{u, v} B} (g : P ⟶ Q) (h : Q ⟶ U) :
    postcomp T (g ≫ h) = postcomp T g ≫ postcomp T h := sorry

/-- Passing concrete postcomposition to the DG homotopy category agrees with the map of the
fixed-source internal-Hom DG functor. -/
theorem postcomp_toK (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    {P Q : DifferentialGradedModule.{u, v} B} (g : P ⟶ Q) :
    (DifferentialGradedModule.toK A).map (postcomp T g) =
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.map
        ((DifferentialGradedModule.toK B).map g) := sorry

/-- The degreewise family obtained by precomposing a homogeneous map with a bimodule
morphism belongs to the graded-Hom submodule. -/
theorem precompValue_mem (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B)
    (k : ℤ) (g : DifferentialGradedModule.GradedHom B T'.toRightModule P k) :
    (fun n ↦ (g n).comp (f.hom n)) ∈
      DifferentialGradedModule.gradedHomSubmodule B T.toRightModule P k := sorry

/-- Precomposition of one homogeneous right-`B`-linear map by a bimodule morphism. -/
def precompValue (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B) (k : ℤ)
    (g : DifferentialGradedModule.GradedHom B T'.toRightModule P k) :
    DifferentialGradedModule.GradedHom B T.toRightModule P k :=
  ⟨fun n ↦ (g n).comp (f.hom n), precompValue_mem f P k g⟩

/-- Precomposition is additive on each homogeneous internal-Hom component. -/
theorem precompValue_add (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B)
    (k : ℤ) (g h : DifferentialGradedModule.GradedHom B T'.toRightModule P k) :
    precompValue f P k (g + h) = precompValue f P k g + precompValue f P k h := sorry

/-- Precomposition is `R`-linear on each homogeneous internal-Hom component. -/
theorem precompValue_smul (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B)
    (k : ℤ) (r : R) (g : DifferentialGradedModule.GradedHom B T'.toRightModule P k) :
    precompValue f P k (r • g) = r • precompValue f P k g := sorry

/-- Precomposition as a linear map on the degree-`k` internal-Hom component. -/
def precompLinear (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    DifferentialGradedBimodule.internalHomFamily T' P k →ₗ[R]
      DifferentialGradedBimodule.internalHomFamily T P k where
  toFun := precompValue f P k
  map_add' := precompValue_add f P k
  map_smul' := precompValue_smul f P k

/-- Precomposition commutes with the internal-Hom differential. -/
theorem precompLinear_comm_d (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B)
    (k : ℤ) (g : DifferentialGradedBimodule.internalHomFamily T' P k) :
    precompLinear f P (k + 1)
        (DifferentialGradedBimodule.internalHomDifferential T' P k g) =
      DifferentialGradedBimodule.internalHomDifferential T P k
        (precompLinear f P k g) := sorry

/-- Precomposition respects the right `A`-action on fixed-source internal Hom. -/
theorem precompLinear_comm_smul (f : T ⟶ T')
    (P : DifferentialGradedModule.{u, v} B) (p i : ℤ)
    (g : (DifferentialGradedBimodule.internalHom T' P).X p) (a : A.X i) :
    precompLinear f P (p + i)
        ((DifferentialGradedBimodule.internalHom T' P).smul p i g a) =
      (DifferentialGradedBimodule.internalHom T P).smul p i
        (precompLinear f P p g) a := sorry

/-- A bimodule morphism acts contravariantly on fixed-source internal Hom by precomposition. -/
@[stacks 09LN "precomposition on fixed-source DG internal Hom"]
def precomp (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedBimodule.internalHom T' P ⟶
      DifferentialGradedBimodule.internalHom T P where
  hom k := precompLinear f P k
  comm_d := precompLinear_comm_d f P
  comm_smul := precompLinear_comm_smul f P

/-- Evaluating the precomposition map is ordinary degreewise composition. -/
@[simp]
theorem precomp_apply (f : T ⟶ T') (P : DifferentialGradedModule.{u, v} B)
    (k n : ℤ) (g : DifferentialGradedModule.GradedHom B T'.toRightModule P k)
    (x : T.X n) :
    DifferentialGradedBimodule.asGradedHom T P ((precomp f P).hom k g) n x =
      g n (f.hom n x) := sorry

/-- Precomposition is additive in the bimodule morphism. -/
@[simp]
theorem precomp_add (f g : T ⟶ T') (P : DifferentialGradedModule.{u, v} B) :
    precomp (f + g) P = precomp f P + precomp g P := sorry

/-- Precomposition is `R`-linear in the bimodule morphism. -/
@[simp]
theorem precomp_smul (r : R) (f : T ⟶ T')
    (P : DifferentialGradedModule.{u, v} B) :
    precomp (r • f) P = r • precomp f P := sorry

/-- The precomposition components are natural in the target DG module on the closed category. -/
theorem precompComp_naturality (f : T ⟶ T')
    {P Q : Comp R (DifferentialGradedModule.{u, v} B)} (g : P ⟶ Q) :
    (DifferentialGradedBimodule.internalHomDgFunctor T').mapComp.map g ≫
        DifferentialGradedModule.homToCompHom (precomp f Q.obj) =
      DifferentialGradedModule.homToCompHom (precomp f P.obj) ≫
        (DifferentialGradedBimodule.internalHomDgFunctor T).mapComp.map g := sorry

/-- Precomposition by a bimodule morphism as a natural transformation on closed degree-zero
morphisms. -/
@[stacks 09LN "closed DG internal Hom precomposition"]
def precompComp (f : T ⟶ T') :
    (DifferentialGradedBimodule.internalHomDgFunctor T').mapComp ⟶
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapComp where
  app P := DifferentialGradedModule.homToCompHom (precomp f P.obj)
  naturality := fun {P Q} g ↦
    precompComp_naturality (T := T) (T' := T') f (P := P) (Q := Q) g

/-- The component of `precompComp` is represented by the explicit precomposition map. -/
@[simp]
theorem precompComp_app (f : T ⟶ T')
    (P : Comp R (DifferentialGradedModule.{u, v} B)) :
    (precompComp f).app P =
      DifferentialGradedModule.homToCompHom (precomp f P.obj) := sorry

/-- Closed precomposition transformations are additive in the bimodule morphism. -/
@[simp]
theorem precompComp_add (f g : T ⟶ T') :
    precompComp (f + g) = precompComp f + precompComp g := sorry

/-- Closed precomposition transformations are `R`-linear in the bimodule morphism. -/
@[simp]
theorem precompComp_smul (r : R) (f : T ⟶ T') :
    precompComp (r • f) = r • precompComp f := sorry

/-- The precomposition components are natural after passing to homotopy classes. -/
theorem precompK_naturality (f : T ⟶ T')
    {P Q : K R (DifferentialGradedModule.{u, v} B)} (g : P ⟶ Q) :
    (DifferentialGradedBimodule.internalHomDgFunctor T').mapK.map g ≫
        ((precompComp f).app
          (⟨Q.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK =
      ((precompComp f).app
          (⟨P.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK ≫
        (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.map g := sorry

/-- Precomposition by a bimodule morphism as a natural transformation on DG homotopy
categories. -/
@[stacks 09LN "homotopy DG internal Hom precomposition"]
def precompK (f : T ⟶ T') :
    (DifferentialGradedBimodule.internalHomDgFunctor T').mapK ⟶
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapK where
  app P := ((precompComp f).app
    (⟨P.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK
  naturality := fun {P Q} g ↦
    precompK_naturality (T := T) (T' := T') f (P := P) (Q := Q) g

/-- The homotopy-category component of precomposition is represented by the concrete closed
map. -/
@[simp]
theorem precompK_app (f : T ⟶ T')
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    (precompK f).app P = ((precompComp f).app
      (⟨P.obj⟩ : Comp R (DifferentialGradedModule.{u, v} B))).inK := sorry

/-- Homotopy precomposition transformations are additive in the bimodule morphism. -/
@[simp]
theorem precompK_add (f g : T ⟶ T') :
    precompK (f + g) = precompK f + precompK g := sorry

/-- Homotopy precomposition transformations are `R`-linear in the bimodule morphism. -/
@[simp]
theorem precompK_smul (r : R) (f : T ⟶ T') :
    precompK (r • f) = r • precompK f := sorry

/-- Precomposition by the identity bimodule morphism is the identity on the closed category. -/
@[simp]
theorem precompComp_id (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    precompComp (𝟙 T) = 𝟙 (DifferentialGradedBimodule.internalHomDgFunctor T).mapComp := sorry

/-- Contravariant precomposition reverses composition on the closed category. -/
@[simp]
theorem precompComp_comp (f : T ⟶ T') (g : T' ⟶ T'') :
    precompComp (f ≫ g) = precompComp g ≫ precompComp f := sorry

/-- Precomposition by the identity bimodule morphism is the identity on the homotopy category. -/
@[simp]
theorem precompK_id (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    precompK (𝟙 T) = 𝟙 (DifferentialGradedBimodule.internalHomDgFunctor T).mapK := sorry

/-- Contravariant precomposition reverses composition on the homotopy category. -/
@[simp]
theorem precompK_comp (f : T ⟶ T') (g : T' ⟶ T'') :
    precompK (f ≫ g) = precompK g ≫ precompK f := sorry

namespace Closed

/-- Closed internal-Hom functors, contravariantly parametrized by the differential graded
bimodule. -/
@[stacks 09LN "closed DG internal Hom functor parametrized by the bimodule"]
def bimoduleFunctor :
    (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ ⥤
      (Comp R (DifferentialGradedModule.{u, v} B) ⥤
        Comp R (DifferentialGradedModule.{u, v} A)) where
  obj T := (DifferentialGradedBimodule.internalHomDgFunctor T.unop).mapComp
  map f := precompComp f.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluating the closed bimodule-parameter internal-Hom functor gives the fixed-source
functor. -/
@[simp]
theorem bimoduleFunctor_obj (T : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ) :
    (bimoduleFunctor (A := A) (B := B)).obj T =
      (DifferentialGradedBimodule.internalHomDgFunctor T.unop).mapComp := sorry

/-- The closed bimodule-parameter internal-Hom functor maps an opposite morphism by
precomposition. -/
@[simp]
theorem bimoduleFunctor_map
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (f : T ⟶ T') :
    (bimoduleFunctor (A := A) (B := B)).map f = precompComp f.unop := sorry

/-- The closed internal-Hom parameter functor preserves addition of opposite bimodule
morphisms. -/
@[simp]
theorem bimoduleFunctor_map_add
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (f g : T ⟶ T') :
    (bimoduleFunctor (A := A) (B := B)).map (f + g) =
      (bimoduleFunctor (A := A) (B := B)).map f +
        (bimoduleFunctor (A := A) (B := B)).map g := sorry

/-- The closed internal-Hom parameter functor is additive. -/
@[stacks 09LN "additive closed DG internal Hom parameter functor"]
instance bimoduleFunctorAdditive :
    (bimoduleFunctor (A := A) (B := B)).Additive := sorry

/-- The closed internal-Hom parameter functor preserves scalar multiplication of opposite
bimodule morphisms. -/
@[simp]
theorem bimoduleFunctor_map_smul
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (r : R) (f : T ⟶ T') :
    (bimoduleFunctor (A := A) (B := B)).map (r • f) =
      r • (bimoduleFunctor (A := A) (B := B)).map f := sorry

/-- The closed internal-Hom parameter functor is `R`-linear. -/
@[stacks 09LN "linear closed DG internal Hom parameter functor"]
instance bimoduleFunctorLinear :
    Functor.Linear R (bimoduleFunctor (A := A) (B := B)) := sorry

end Closed

namespace Homotopy

/-- Homotopy internal-Hom functors, contravariantly parametrized by the differential graded
bimodule. -/
@[stacks 09LT "homotopy DG internal Hom functor parametrized by the bimodule"]
def bimoduleFunctor :
    (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ ⥤
      (K R (DifferentialGradedModule.{u, v} B) ⥤
        K R (DifferentialGradedModule.{u, v} A)) where
  obj T := (DifferentialGradedBimodule.internalHomDgFunctor T.unop).mapK
  map f := precompK f.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluating the homotopy bimodule-parameter internal-Hom functor gives the fixed-source
functor. -/
@[simp]
theorem bimoduleFunctor_obj (T : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ) :
    (bimoduleFunctor (A := A) (B := B)).obj T =
      (DifferentialGradedBimodule.internalHomDgFunctor T.unop).mapK := sorry

/-- The homotopy bimodule-parameter internal-Hom functor maps an opposite morphism by
precomposition. -/
@[simp]
theorem bimoduleFunctor_map
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (f : T ⟶ T') :
    (bimoduleFunctor (A := A) (B := B)).map f = precompK f.unop := sorry

/-- The homotopy internal-Hom parameter functor preserves addition of opposite bimodule
morphisms. -/
@[simp]
theorem bimoduleFunctor_map_add
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (f g : T ⟶ T') :
    (bimoduleFunctor (A := A) (B := B)).map (f + g) =
      (bimoduleFunctor (A := A) (B := B)).map f +
        (bimoduleFunctor (A := A) (B := B)).map g := sorry

/-- The homotopy internal-Hom parameter functor is additive. -/
@[stacks 09LT "additive homotopy DG internal Hom parameter functor"]
instance bimoduleFunctorAdditive :
    (bimoduleFunctor (A := A) (B := B)).Additive := sorry

/-- The homotopy internal-Hom parameter functor preserves scalar multiplication of opposite
bimodule morphisms. -/
@[simp]
theorem bimoduleFunctor_map_smul
    {T T' : (DifferentialGradedBimodule.{u, v, w, x} A B)ᵒᵖ} (r : R) (f : T ⟶ T') :
    (bimoduleFunctor (A := A) (B := B)).map (r • f) =
      r • (bimoduleFunctor (A := A) (B := B)).map f := sorry

/-- The homotopy internal-Hom parameter functor is `R`-linear. -/
@[stacks 09LT "linear homotopy DG internal Hom parameter functor"]
instance bimoduleFunctorLinear :
    Functor.Linear R (bimoduleFunctor (A := A) (B := B)) := sorry

end Homotopy

/-- The closed precomposition transformations associated to an isomorphism are inverse. -/
theorem precompCompIso_hom_inv_id (e : T ≅ T') :
    precompComp e.hom ≫ precompComp e.inv =
      𝟙 (DifferentialGradedBimodule.internalHomDgFunctor T').mapComp := sorry

/-- The inverse and forward closed precomposition transformations associated to an isomorphism
are inverse. -/
theorem precompCompIso_inv_hom_id (e : T ≅ T') :
    precompComp e.inv ≫ precompComp e.hom =
      𝟙 (DifferentialGradedBimodule.internalHomDgFunctor T).mapComp := sorry

/-- A bimodule isomorphism induces a contravariant natural isomorphism of fixed-source internal
Hom functors on closed morphisms. -/
def precompCompIso (e : T ≅ T') :
    (DifferentialGradedBimodule.internalHomDgFunctor T').mapComp ≅
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapComp where
  hom := precompComp e.hom
  inv := precompComp e.inv
  hom_inv_id := precompCompIso_hom_inv_id e
  inv_hom_id := precompCompIso_inv_hom_id e

/-- The homotopy precomposition transformations associated to an isomorphism are inverse. -/
theorem precompKIso_hom_inv_id (e : T ≅ T') :
    precompK e.hom ≫ precompK e.inv =
      𝟙 (DifferentialGradedBimodule.internalHomDgFunctor T').mapK := sorry

/-- The inverse and forward homotopy precomposition transformations associated to an
isomorphism are inverse. -/
theorem precompKIso_inv_hom_id (e : T ≅ T') :
    precompK e.inv ≫ precompK e.hom =
      𝟙 (DifferentialGradedBimodule.internalHomDgFunctor T).mapK := sorry

/-- A bimodule isomorphism induces a contravariant natural isomorphism of fixed-source internal
Hom functors on DG homotopy categories. -/
def precompKIso (e : T ≅ T') :
    (DifferentialGradedBimodule.internalHomDgFunctor T').mapK ≅
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapK where
  hom := precompK e.hom
  inv := precompK e.inv
  hom_inv_id := precompKIso_hom_inv_id e
  inv_hom_id := precompKIso_inv_hom_id e

#synth (Closed.bimoduleFunctor (A := A) (B := B)).Additive
#synth Functor.Linear R (Closed.bimoduleFunctor (A := A) (B := B))
#synth (Homotopy.bimoduleFunctor (A := A) (B := B)).Additive
#synth Functor.Linear R (Homotopy.bimoduleFunctor (A := A) (B := B))

end DifferentialGradedBimodule.InternalHom
