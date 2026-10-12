/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import stacks_project.Chap75.Lemma_75_10_4_HomSequence
public import stacks_project.Chap75.Lemma_75_10_7_Comparison

/-!
# Glueing objects of `D(𝒪)` along an elementary distinguished square

An elementary distinguished square `(j : U ⟶ X, f : V ⟶ X)` and glueing data
`(A, B, c)` in `D(𝒪_U)`, `D(𝒪_V)` determine the canonical morphism
`Rj_{U,*} A ⊞ Rj_{V,*} B ⟶ Rj_{W,*}(B|_W)` on `W = U ×_X V`. Completing that
morphism as the second arrow of a distinguished triangle produces an object of
`D(𝒪_X)` together with restriction maps to `A` and `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [IsElementaryDistinguishedSquare j f]
variable [(restrictFunctor (fiberHom j f)).Additive]
variable [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
variable [(restrictFunctor (Limits.pullback.fst j f)).Additive]
variable [(restrictFunctor (Limits.pullback.snd j f)).Additive]
variable [(restrictFunctor (Limits.pullback.snd j f ≫ f)).Additive]
variable [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteLimits (restrictFunctor j)]
variable [PreservesFiniteColimits (restrictFunctor j)]
variable [PreservesFiniteLimits (restrictFunctor f)]
variable [PreservesFiniteColimits (restrictFunctor f)]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.fst j f))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.fst j f))]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.snd j f))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.snd j f))]
variable [PreservesFiniteLimits (restrictFunctor (Limits.pullback.snd j f ≫ f))]
variable [PreservesFiniteColimits (restrictFunctor (Limits.pullback.snd j f ≫ f))]

/-- The `U`-leg `Rj_{U,*} A ⟶ Rj_{W,*}(A|_W)` of glueing, obtained by adjoining the
restricted counit of `j^* ⊣ Rj_{U,*}` along `W ⟶ U ⟶ X`. -/
def moduleDerivedGlueDiffUAdjunct (A : ModuleDerived U) :
    (pushforwardDerived j).obj A ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (Limits.pullback.fst j f)).obj A) :=
  (restrictPushforwardDerivedAdjunction (fiberHom j f)).homEquiv
      ((pushforwardDerived j).obj A)
      ((restrictFunctorDerived (Limits.pullback.fst j f)).obj A)
      ((restrictFunctorDerivedCompIso j (Limits.pullback.fst j f)).inv.app
          ((pushforwardDerived j).obj A) ≫
        (restrictFunctorDerived (Limits.pullback.fst j f)).map
          ((restrictPushforwardDerivedAdjunction j).counit.app A))

/-- The `U`-leg of the glueing morphism
`Rj_{U,*} A ⟶ Rj_{W,*}(B|_W)`, as the adjunct along `j` followed by `Rj_{W,*} c`. -/
def moduleDerivedGlueDiffU (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (pushforwardDerived j).obj A ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :=
  moduleDerivedGlueDiffUAdjunct j f A ≫
    (pushforwardDerived (fiberHom j f)).map c.hom

/-- `moduleDerivedGlueDiffU` is the `j`-adjunct of the restricted counit, postcomposed
with `Rj_{W,*} c`. -/
theorem moduleDerivedGlueDiffU_eq (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    moduleDerivedGlueDiffU j f A B c =
      moduleDerivedGlueDiffUAdjunct j f A ≫
        (pushforwardDerived (fiberHom j f)).map c.hom :=
  sorry

/-- The obvious `V`-leg `Rj_{V,*} B ⟶ Rj_{W,*}(B|_W)` of glueing, identifying
`(Rf_* B)|_W` with `B|_W` via successive restriction and the counit of
`f^* ⊣ Rf_*`. -/
def moduleDerivedGlueDiffV (B : ModuleDerived V) :
    (pushforwardDerived f).obj B ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :=
  (restrictPushforwardDerivedAdjunction (fiberHom j f)).homEquiv
      ((pushforwardDerived f).obj B)
      ((restrictFunctorDerived (Limits.pullback.snd j f)).obj B)
      ((restrictFunctorDerived_eqToIso (fiberHom_eq j f)).hom.app
          ((pushforwardDerived f).obj B) ≫
        (restrictFunctorDerivedCompIso f (Limits.pullback.snd j f)).inv.app
          ((pushforwardDerived f).obj B) ≫
        (restrictFunctorDerived (Limits.pullback.snd j f)).map
          ((restrictPushforwardDerivedAdjunction f).counit.app B))

/-- `moduleDerivedGlueDiffV` is the adjunct of the counit of `f^* ⊣ Rf_*` after
identifying restriction along `fiberHom` with restriction along `V`. -/
theorem moduleDerivedGlueDiffV_eq (B : ModuleDerived V) :
    moduleDerivedGlueDiffV j f B =
      (restrictPushforwardDerivedAdjunction (fiberHom j f)).homEquiv
          ((pushforwardDerived f).obj B)
          ((restrictFunctorDerived (Limits.pullback.snd j f)).obj B)
          ((restrictFunctorDerived_eqToIso (fiberHom_eq j f)).hom.app
              ((pushforwardDerived f).obj B) ≫
            (restrictFunctorDerivedCompIso f (Limits.pullback.snd j f)).inv.app
              ((pushforwardDerived f).obj B) ≫
            (restrictFunctorDerived (Limits.pullback.snd j f)).map
              ((restrictPushforwardDerivedAdjunction f).counit.app B)) :=
  sorry

/-- The canonical glueing morphism
`Rj_{U,*} A ⊞ Rj_{V,*} B ⟶ Rj_{W,*}(B|_W)` with no Mayer–Vietoris minus sign. -/
def moduleDerivedGlueDiff (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    biprod ((pushforwardDerived j).obj A) ((pushforwardDerived f).obj B) ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :=
  biprod.desc (moduleDerivedGlueDiffU j f A B c) (moduleDerivedGlueDiffV j f B)

/-- Chosen distinguished triangle in `D(𝒪_X)` completing `moduleDerivedGlueDiff` as
its second arrow. -/
def moduleDerivedGlueTriangle (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    Triangle (ModuleDerived X) :=
  let h := distinguished_cocone_triangle₁ (moduleDerivedGlueDiff j f A B c)
  Triangle.mk (Classical.choose (Classical.choose_spec h))
    (moduleDerivedGlueDiff j f A B c)
    (Classical.choose (Classical.choose_spec (Classical.choose_spec h)))

/-- The second vertex of `moduleDerivedGlueTriangle` is
`Rj_{U,*} A ⊞ Rj_{V,*} B`. -/
theorem moduleDerivedGlueTriangle_obj₂ (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (moduleDerivedGlueTriangle j f A B c).obj₂ =
      biprod ((pushforwardDerived j).obj A) ((pushforwardDerived f).obj B) :=
  sorry

/-- The third vertex of `moduleDerivedGlueTriangle` is `Rj_{W,*}(B|_W)`. -/
theorem moduleDerivedGlueTriangle_obj₃ (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (moduleDerivedGlueTriangle j f A B c).obj₃ =
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :=
  sorry

/-- The second arrow of `moduleDerivedGlueTriangle` is `moduleDerivedGlueDiff`. -/
theorem moduleDerivedGlueTriangle_mor₂ (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (moduleDerivedGlueTriangle j f A B c).mor₂ = moduleDerivedGlueDiff j f A B c :=
  sorry

/-- `moduleDerivedGlueTriangle` is a distinguished triangle in `D(𝒪_X)`. -/
theorem moduleDerivedGlueTriangle_mem_distTriang (A : ModuleDerived U)
    (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    moduleDerivedGlueTriangle j f A B c ∈ distTriang (ModuleDerived X) :=
  sorry

/-- The object of `D(𝒪_X)` obtained by completing the glueing morphism of `(A, B, c)`
as a distinguished triangle. -/
def moduleDerivedGlue (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    ModuleDerived X :=
  (moduleDerivedGlueTriangle j f A B c).obj₁

/-- The first arrow of the glueing triangle,
`F ⟶ Rj_{U,*} A ⊞ Rj_{V,*} B`. -/
def moduleDerivedGlueι (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    moduleDerivedGlue j f A B c ⟶
      biprod ((pushforwardDerived j).obj A) ((pushforwardDerived f).obj B) :=
  (moduleDerivedGlueTriangle j f A B c).mor₁

/-- The restriction morphism `F|_U ⟶ A` of the glued object, as the `U`-component of
`moduleDerivedGlueι` followed by the counit of `j^* ⊣ Rj_{U,*}`. -/
def moduleDerivedGlueHomU (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (restrictFunctorDerived j).obj (moduleDerivedGlue j f A B c) ⟶ A :=
  (restrictFunctorDerived j).map (moduleDerivedGlueι j f A B c ≫ biprod.fst) ≫
    (restrictPushforwardDerivedAdjunction j).counit.app A

/-- The restriction morphism `F|_V ⟶ B` of the glued object, as the `V`-component of
`moduleDerivedGlueι` followed by the counit of `f^* ⊣ Rf_*`. -/
def moduleDerivedGlueHomV (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (restrictFunctorDerived f).obj (moduleDerivedGlue j f A B c) ⟶ B :=
  (restrictFunctorDerived f).map (moduleDerivedGlueι j f A B c ≫ biprod.snd) ≫
    (restrictPushforwardDerivedAdjunction f).counit.app B

/-- The restriction `F|_U ⟶ A` is an isomorphism. -/
instance isIso_moduleDerivedGlueHomU (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    IsIso (moduleDerivedGlueHomU j f A B c) :=
  sorry

/-- The restriction `F|_V ⟶ B` is an isomorphism. -/
instance isIso_moduleDerivedGlueHomV (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    IsIso (moduleDerivedGlueHomV j f A B c) :=
  sorry

/-- The restriction isomorphism `F|_U ≅ A` of the glued object. -/
def moduleDerivedGlueIsoU (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (restrictFunctorDerived j).obj (moduleDerivedGlue j f A B c) ≅ A :=
  asIso (moduleDerivedGlueHomU j f A B c)

/-- The restriction isomorphism `F|_V ≅ B` of the glued object. -/
def moduleDerivedGlueIsoV (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (restrictFunctorDerived f).obj (moduleDerivedGlue j f A B c) ≅ B :=
  asIso (moduleDerivedGlueHomV j f A B c)

/-- Identification of the two successive restrictions of the glued object to
`W = U ×_X V`. -/
def moduleDerivedGlueOverlapIso (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    (restrictFunctorDerived (Limits.pullback.fst j f)).obj
        ((restrictFunctorDerived j).obj (moduleDerivedGlue j f A B c)) ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj
        ((restrictFunctorDerived f).obj (moduleDerivedGlue j f A B c)) :=
  (restrictFunctorDerivedCompIso j (Limits.pullback.fst j f)).app
      (moduleDerivedGlue j f A B c) ≪≫
    (restrictFunctorDerived_eqToIso (fiberHom_eq j f)).app
      (moduleDerivedGlue j f A B c) ≪≫
    (restrictFunctorDerivedCompIso f (Limits.pullback.snd j f)).symm.app
      (moduleDerivedGlue j f A B c)

/-- Compatibility `c = g|_W ∘ f⁻¹|_W` of the glueing isomorphism with the restriction
isomorphisms of `moduleDerivedGlue`. -/
theorem moduleDerivedGlue_compat (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    c.hom =
      (restrictFunctorDerived (Limits.pullback.fst j f)).map
          (moduleDerivedGlueIsoU j f A B c).inv ≫
        (moduleDerivedGlueOverlapIso j f A B c).hom ≫
        (restrictFunctorDerived (Limits.pullback.snd j f)).map
          (moduleDerivedGlueIsoV j f A B c).hom :=
  sorry

/-- Restriction of a morphism `A ⟶ E|_U` to `W = U ×_X V`, as a morphism
`A|_W ⟶ E|_W`. -/
def moduleDerivedGlueRestrictU {A : ModuleDerived U} {E : ModuleDerived X}
    (a : A ⟶ (restrictFunctorDerived j).obj E) :
    (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ⟶
      (restrictFunctorDerived (fiberHom j f)).obj E :=
  (restrictFunctorDerived (Limits.pullback.fst j f)).map a ≫
    (restrictFunctorDerivedCompIso j (Limits.pullback.fst j f)).hom.app E

/-- Restriction of a morphism `B ⟶ E|_V` to `W = U ×_X V`, as a morphism
`B|_W ⟶ E|_W`. -/
def moduleDerivedGlueRestrictV {B : ModuleDerived V} {E : ModuleDerived X}
    (b : B ⟶ (restrictFunctorDerived f).obj E) :
    (restrictFunctorDerived (Limits.pullback.snd j f)).obj B ⟶
      (restrictFunctorDerived (fiberHom j f)).obj E :=
  (restrictFunctorDerived (Limits.pullback.snd j f)).map b ≫
    (restrictFunctorDerivedCompIso f (Limits.pullback.snd j f)).hom.app E ≫
    (restrictFunctorDerived_eqToIso (fiberHom_eq j f).symm).hom.app E

/-- Compatibility of a pair of morphisms `A ⟶ E|_U` and `B ⟶ E|_V` with an overlap
isomorphism `c` on `W = U ×_X V`. -/
def moduleDerivedGlueHomCompatible (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B)
    (E : ModuleDerived X) (a : A ⟶ (restrictFunctorDerived j).obj E)
    (b : B ⟶ (restrictFunctorDerived f).obj E) : Prop :=
  moduleDerivedGlueRestrictU j f a = c.hom ≫ moduleDerivedGlueRestrictV j f b

end AlgebraicGeometry.AlgebraicSpace.Modules
