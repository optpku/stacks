/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReasLib.AlgebraicTopology.SimplexCategory.Objwise
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation.Zero
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Functoriality
public import ReasLib.CategoryTheory.Limits.Shapes.PositivePowers
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The zero coskeleton as finite self-products

For a fixed object `X`, only the nonempty finite self-products of `X` are needed to construct the
explicit zero-coskeleton model.  This object-specific layer is accompanied by its projection and
Hom-equivalence API, then compared with Mathlib's globally finite-product Cech-nerve owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.ZeroCoskeleton

variable {C : Type u} [Category.{v} C]

section SelfProducts

variable (X : C)
variable [HasPositivePowers X]

/-- The explicit zero-coskeleton model whose degree `n` is the `(n + 1)`-fold self-product of
`X`, obtained from the generic indexed-product functor. -/
@[stacks 0182 "zero coskeleton as finite self-products"]
noncomputable def selfProduct : SimplicialObject C :=
  Functor.indexedProd (forget SimplexCategory)
    ((Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The value of the self-product zero coskeleton at `Delta` is the positive power indexed by
the vertices of `Delta`. -/
@[simp, stacks 0182 "zero coskeleton object formula"]
theorem selfProduct.obj (Delta : SimplexCategoryᵒᵖ) :
    (selfProduct X).obj Delta = ∏ᶜ (fun _ : Fin (Delta.unop.len + 1) ↦ X) := sorry

/-- A simplex operator on the self-product zero coskeleton reindexes product projections. -/
@[simp, reassoc, stacks 0182 "zero-coskeleton self-product projection formula"]
theorem selfProduct.map.π {Delta Delta' : SimplexCategoryᵒᵖ}
    (f : Delta ⟶ Delta') (i : Fin (Delta'.unop.len + 1)) :
    (selfProduct X).map f ≫ Pi.π (fun _ : Fin (Delta'.unop.len + 1) ↦ X) i =
      Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ X) (f.unop.toOrderHom i) := sorry

namespace selfProduct

/-- A morphism of objects induces the degreewise product morphism between their self-product
zero coskeletons. -/
@[stacks 0182 "functoriality of the self-product zero coskeleton"]
noncomputable def map {A B : C} [HasPositivePowers A] [HasPositivePowers B]
    (f : A ⟶ B) : selfProduct A ⟶ selfProduct B :=
  Functor.indexedProd.hom (forget SimplexCategory)
    ((Functor.const SimplexCategoryᵒᵖ).map f)

/-- The component of the morphism induced between self-product zero coskeletons. -/
@[simp, stacks 0182 "self-product morphism component"]
theorem map_app {A B : C} [HasPositivePowers A] [HasPositivePowers B]
    (f : A ⟶ B) (Delta : SimplexCategoryᵒᵖ) :
    (map f).app Delta = Functor.indexedProd.homApp
      (forget SimplexCategory) ((Functor.const SimplexCategoryᵒᵖ).map f) Delta := sorry

/-- The induced morphism acts on every self-product factor by the original morphism. -/
@[reassoc (attr := simp), stacks 0182 "self-product morphism projection formula"]
theorem map.app_π {A B : C} [HasPositivePowers A] [HasPositivePowers B]
    (f : A ⟶ B) (Delta : SimplexCategoryᵒᵖ)
    (i : Fin (Delta.unop.len + 1)) :
    (map f).app Delta ≫ Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ B) i =
      Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ A) i ≫ f := sorry

/-- The self-product construction sends identity morphisms to identity morphisms. -/
@[simp, stacks 0182 "self-product identity morphism"]
theorem map_id (A : C) [HasPositivePowers A] :
    map (𝟙 A) = 𝟙 (selfProduct A) := sorry

/-- The self-product construction sends composites to composites. -/
@[stacks 0182 "self-product composition of morphisms"]
theorem map_comp {A B D : C} [HasPositivePowers A] [HasPositivePowers B]
    [HasPositivePowers D] (f : A ⟶ B) (g : B ⟶ D) :
    map (f ≫ g) = map f ≫ map g := sorry

end selfProduct

/-- The degreewise map into the self-product model induced by a map from zero-simplices. -/
@[stacks 0182 "degreewise map into the zero coskeleton"]
noncomputable def lift.component {V : SimplicialObject C} (g : V _⦋0⦌ ⟶ X)
    (Delta : SimplexCategoryᵒᵖ) : V.obj Delta ⟶ (selfProduct X).obj Delta :=
  (Pi.lift (fun i ↦ V.map (SimplexCategory.const ⦋0⦌ Delta.unop i).op ≫ g) :
    V.obj Delta ⟶ ∏ᶜ fun _ : Fin (Delta.unop.len + 1) ↦ X)

/-- Projecting the degreewise map reconstructed from degree zero recovers the corresponding
vertex map followed by the given degree-zero morphism. -/
@[reassoc (attr := simp), stacks 0182 "degreewise zero-coskeleton projection formula"]
theorem lift.component_π {V : SimplicialObject C} (g : V _⦋0⦌ ⟶ X)
    (Delta : SimplexCategoryᵒᵖ) (i : Fin (Delta.unop.len + 1)) :
    lift.component X g Delta ≫
        Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ X) i =
      V.map (SimplexCategory.const ⦋0⦌ Delta.unop i).op ≫ g := sorry

/-- The degreewise maps induced from zero-simplices are natural. -/
@[stacks 0182 "degreewise zero-coskeleton lift naturality"]
theorem lift.naturality {V : SimplicialObject C} (g : V _⦋0⦌ ⟶ X)
    {Delta Delta' : SimplexCategoryᵒᵖ} (f : Delta ⟶ Delta') :
    V.map f ≫ lift.component X g Delta' =
      lift.component X g Delta ≫ (selfProduct X).map f := sorry

/-- Reconstruct a simplicial morphism into the zero-coskeleton model from its degree-zero map. -/
@[stacks 0182 "map into the zero coskeleton from degree zero"]
noncomputable def lift (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X) :
    V ⟶ selfProduct X where
  app := lift.component X g
  naturality := fun {_ _} f ↦ lift.naturality X g f

/-- The component of the map reconstructed from its degree-zero value. -/
@[simp, stacks 0182 "map into the zero coskeleton component"]
theorem lift.app (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X)
    (Delta : SimplexCategoryᵒᵖ) :
    (lift X V g).app Delta = lift.component X g Delta := sorry

/-- Each projection of the simplicial morphism reconstructed from degree zero is the
corresponding vertex map followed by the original morphism. -/
@[reassoc (attr := simp), stacks 0182 "zero-coskeleton morphism projection formula"]
theorem lift.app_π (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X)
    (Delta : SimplexCategoryᵒᵖ) (i : Fin (Delta.unop.len + 1)) :
    (lift X V g).app Delta ≫
        Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ X) i =
      V.map (SimplexCategory.const ⦋0⦌ Delta.unop i).op ≫ g := sorry

/-- Evaluate a map into the self-product zero-coskeleton at degree zero and its unique
product projection. -/
@[stacks 0182 "degree-zero projection from the zero coskeleton"]
noncomputable def zeroProjection (V : SimplicialObject C)
    (f : V ⟶ selfProduct X) : V _⦋0⦌ ⟶ X :=
  f.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0

/-- Reconstructing from the degree-zero projection of a map into the self-product model returns
the original map. -/
@[stacks 0182 "zero-coskeleton lift after projection"]
theorem lift.zeroProjection (V : SimplicialObject C) (f : V ⟶ selfProduct X) :
    lift X V (zeroProjection X V f) = f := sorry

/-- The degree-zero projection of the reconstructed map is the original degree-zero map. -/
@[stacks 0182 "zero-coskeleton projection after lift"]
theorem zeroProjection.lift (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X) :
    zeroProjection X V (lift X V g) = g := sorry

/-- Maps into the self-product zero coskeleton are canonically equivalent to maps from degree
zero. -/
@[stacks 0182 "universal property of the zero coskeleton"]
noncomputable def homEquiv (V : SimplicialObject C) :
    (V ⟶ selfProduct X) ≃ (V _⦋0⦌ ⟶ X) where
  toFun := zeroProjection X V
  invFun := lift X V
  left_inv := lift.zeroProjection X V
  right_inv := zeroProjection.lift X V

/-- The forward map of the zero-coskeleton Hom equivalence is degree-zero projection. -/
@[simp, stacks 0182 "zero-coskeleton Hom equivalence forward formula"]
theorem homEquiv.apply (V : SimplicialObject C) (f : V ⟶ selfProduct X) :
    homEquiv X V f = zeroProjection X V f := sorry

/-- Every component of a map into the zero coskeleton is recovered from its degree-zero
projection by the corresponding vertex map. -/
@[reassoc (attr := simp), stacks 0182 "arbitrary zero-coskeleton morphism projection formula"]
theorem homEquiv.app_π {V : SimplicialObject C} (f : V ⟶ selfProduct X)
    (Delta : SimplexCategoryᵒᵖ) (i : Fin (Delta.unop.len + 1)) :
    f.app Delta ≫ Pi.π (fun _ : Fin (Delta.unop.len + 1) ↦ X) i =
      V.map (SimplexCategory.const ⦋0⦌ Delta.unop i).op ≫ homEquiv X V f := sorry

/-- The inverse map of the zero-coskeleton Hom equivalence reconstructs the simplicial
morphism from its degree-zero component. -/
@[simp, stacks 0182 "zero-coskeleton Hom equivalence inverse formula"]
theorem homEquiv.symm_apply (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X) :
    (homEquiv X V).symm g = lift X V g := sorry

/-- The zero-coskeleton Hom equivalence is natural by precomposition in the simplicial source. -/
@[stacks 0182 "zero-coskeleton Hom equivalence source naturality"]
theorem homEquiv.precomp {V W : SimplicialObject C} (a : W ⟶ V)
    (f : V ⟶ selfProduct X) :
    homEquiv X W (a ≫ f) = a.app (op ⦋0⦌) ≫ homEquiv X V f := sorry

/-- The self-product zero coskeleton represents maps from degree zero into `X`.  This
object-specific owner requires positive powers only for `X`, unlike the uniform adjunction below. -/
@[stacks 0182 "zero coskeleton represents degree-zero maps"]
noncomputable def representableBy :
    (((evalZero (C := C)).op ⋙ yoneda.obj X).RepresentableBy (selfProduct X)) where
  homEquiv {V} := homEquiv X V
  homEquiv_comp := homEquiv.precomp X

/-- The zero-coskeleton Hom equivalence is natural by postcomposition in the target object. -/
@[stacks 0182 "zero-coskeleton Hom equivalence target naturality"]
theorem homEquiv.postcomp {Y : C} [HasPositivePowers Y] (V : SimplicialObject C)
    (f : X ⟶ Y) (g : V ⟶ selfProduct X) :
    homEquiv Y V (g ≫ selfProduct.map f) = homEquiv X V g ≫ f := sorry

/-- The inverse zero-coskeleton Hom equivalence is natural in the target object. -/
@[stacks 0182 "inverse zero-coskeleton Hom equivalence target naturality"]
theorem homEquiv.symm_postcomp {Y : C} [HasPositivePowers Y]
    (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X) (f : X ⟶ Y) :
    (homEquiv Y V).symm (g ≫ f) =
      (homEquiv X V).symm g ≫ selfProduct.map f := sorry

end SelfProducts

section Functorial

variable [∀ X : C, HasPositivePowers X]

namespace selfProduct

/-- The self-product zero coskeleton as a functor of its degree-zero object. -/
@[stacks 0182 "self-product zero-coskeleton functor"]
noncomputable def functor : C ⥤ SimplicialObject C where
  obj X := selfProduct X
  map f := map f
  map_id X := map_id X
  map_comp f g := map_comp f g

/-- Degree-zero evaluation is left adjoint to the self-product zero-coskeleton functor. -/
@[stacks 0182 "degree-zero self-product adjunction"]
noncomputable def adj : evalZero (C := C) ⊣ functor (C := C) :=
  Adjunction.mkOfHomEquiv {
    homEquiv V X := (ZeroCoskeleton.homEquiv X V).symm
    homEquiv_naturality_left_symm := fun f g ↦ ZeroCoskeleton.homEquiv.precomp _ f g
    homEquiv_naturality_right := fun f g ↦
      ZeroCoskeleton.homEquiv.symm_postcomp _ _ f g }

/-- The self-product zero-coskeleton functor is canonically a right adjoint. -/
@[stacks 0182 "self-product zero-coskeleton right adjoint"]
noncomputable instance (priority := low) isRightAdjoint :
    (functor (C := C)).IsRightAdjoint :=
  ⟨evalZero, ⟨adj⟩⟩

end selfProduct

/-- Under objectwise positive powers, degree-zero evaluation is canonically a left adjoint.
The low priority leaves Mathlib's stronger all-product construction preferred when available. -/
@[stacks 0182 "degree-zero evaluation left adjoint"]
noncomputable instance (priority := low) evalZero.isLeftAdjoint :
    (evalZero (C := C)).IsLeftAdjoint :=
  ⟨selfProduct.functor, ⟨selfProduct.adj⟩⟩

end Functorial

section FiniteProducts

variable [HasFiniteProducts C] (X : C)

namespace cechNerve

/-- The identity components comparing the self-product model with Mathlib's terminal Cech nerve
are natural in the simplex variable. -/
@[stacks 0182 "terminal Cech-nerve comparison naturality"]
theorem terminalIso.naturality {Delta Delta' : SimplexCategoryᵒᵖ}
    (f : Delta ⟶ Delta') :
    (selfProduct X).map f ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (cechNerveTerminalFrom X).map f := sorry

/-- Under global finite products, the object-specific self-product model is the same canonical
simplicial object as Mathlib's `cechNerveTerminalFrom`. -/
@[stacks 0182 "zero coskeleton comparison with the terminal Cech nerve"]
noncomputable def terminalIso : selfProduct X ≅ cechNerveTerminalFrom X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ terminalIso.naturality X f)

/-- The comparison with Mathlib's terminal Čech nerve is degreewise the identity
isomorphism. -/
@[simp, stacks 0182 "terminal Cech-nerve comparison component"]
theorem terminalIso_app (Delta : SimplexCategoryᵒᵖ) :
    (terminalIso X).app Delta = Iso.refl _ := sorry

end cechNerve

end FiniteProducts

end CategoryTheory.SimplicialObject.ZeroCoskeleton
