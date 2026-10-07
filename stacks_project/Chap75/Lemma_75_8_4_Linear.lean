module

public import Mathlib.CategoryTheory.Center.Linear
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

/-!
# Linearity of module sheaves over an affine base

A morphism of algebraic spaces `X ⟶ Spec A` equips `𝒪_X`-modules with an `A`-action.
On each small-étale chart the action is scalar multiplication by the image of `A` in
global functions of the chart; globally it is recorded as a map into the categorical
center, so derived Ext can reuse `Linear.ofRingMorphism` without a global instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The two presentation restrictions agree on the global-sections map of the atlas
structure morphism over `Spec A`. -/
theorem globalSectionsMap_equalizes
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).tAppTop =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).sAppTop :=
  sorry

/-- The structure morphism of an algebraic space over `Spec A` induces the ring map
`A →+* Γ(X, 𝒪_X)`. -/
noncomputable def globalSectionsMap
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    A →+* globalSectionsRing X :=
  (equalizer.lift
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (chosenPresentation X).U.hom.appTop)
      (globalSectionsMap_equalizes f)).hom

/-- After comparison with the chosen atlas, `globalSectionsMap f` recovers the scheme-level
global-sections map of the atlas structure morphism. -/
theorem globalSectionsMap_comp_ι
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    (globalSectionsRing_ι X).hom.comp (globalSectionsMap f) =
      Scheme.Hom.globalSectionsMap (chosenPresentation X).U.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The map `A → Γ(U, 𝒪_U)` induced by the structure morphism of a small-étale
object over `Spec A`. -/
noncomputable def chartSectionsMap (U : smallEtaleSite X) :
    A →+* (structureSheaf X).obj.obj (op U) :=
  ((forget₂ CommRingCat RingCat).map
    (CommRingCat.ofHom
      (Scheme.Hom.globalSectionsMap ((smallEtaleToOver X).obj U).hom))).hom

/-- `chartSectionsMap U` is the global-sections map of the underlying scheme over
`Spec A`. -/
theorem chartSectionsMap_eq (U : smallEtaleSite X) :
    chartSectionsMap U =
      ((forget₂ CommRingCat RingCat).map
        (CommRingCat.ofHom
          (Scheme.Hom.globalSectionsMap ((smallEtaleToOver X).obj U).hom))).hom :=
  sorry

/-- Multiplication by an element of `A` on the sections of a module sheaf over one
small-étale object, via the structure morphism of the underlying scheme. -/
noncomputable abbrev mulApp (a : A) (M : Modules X) (U : (smallEtaleSite X)ᵒᵖ) :
    M.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom
    { toFun := fun m ↦ chartSectionsMap U.unop a • m
      map_add' := sorry
      map_smul' := sorry }

/-- Multiplication by an element of `A` commutes with restriction maps of a module sheaf. -/
theorem mulApp_naturality (a : A) (M : Modules X)
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    M.val.map i ≫
        (ModuleCat.restrictScalars ((structureSheaf X).obj.map i).hom).map
          (mulApp a M V) =
      mulApp a M U ≫ M.val.map i :=
  sorry

/-- Multiplication by an element of `A` as an endomorphism of a module sheaf on `X`. -/
noncomputable def mul (a : A) (M : Modules X) : M ⟶ M where
  val.app U := mulApp a M U
  val.naturality i := mulApp_naturality a M i

/-- Module-sheaf morphisms commute with multiplication by an element of `A`. -/
theorem mul_naturality (a : A) {M N : Modules X} (φ : M ⟶ N) :
    φ ≫ mul a N = mul a M ≫ φ :=
  sorry

/-- An element of `A` determines a central endomorphism of the category of module sheaves. -/
noncomputable def center (a : A) : CatCenter (Modules X) where
  app M := mul a M
  naturality := fun {_ _} φ ↦ mul_naturality a φ

/-- The unit of `A` acts as the identity central endomorphism. -/
theorem center_one (X : AlgebraicSpace (Spec (CommRingCat.of A))) :
    (center (1 : A) : CatCenter (Modules X)) = 1 :=
  sorry

/-- Multiplication in `A` agrees with multiplication in the categorical center. -/
theorem center_mul (X : AlgebraicSpace (Spec (CommRingCat.of A))) (a b : A) :
    (center (a * b) : CatCenter (Modules X)) =
      (center a : CatCenter (Modules X)) * center b :=
  sorry

/-- The zero element of `A` acts as the zero central endomorphism. -/
theorem center_zero (X : AlgebraicSpace (Spec (CommRingCat.of A))) :
    (center (0 : A) : CatCenter (Modules X)) = 0 :=
  sorry

/-- Addition in `A` agrees with addition in the categorical center. -/
theorem center_add (X : AlgebraicSpace (Spec (CommRingCat.of A))) (a b : A) :
    (center (a + b) : CatCenter (Modules X)) =
      (center a : CatCenter (Modules X)) + center b :=
  sorry

/-- The action of `A` on module sheaves induced by a morphism to `Spec A`, as a ring
homomorphism into the categorical center. -/
noncomputable def baseCenterHom
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    A →+* CatCenter (Modules X) where
  toFun := center
  map_one' := center_one X
  map_mul' := center_mul X
  map_zero' := center_zero X
  map_add' := center_add X

/-- The `A`-linear structure on `X.Modules` induced by a morphism to `Spec A`. -/
@[implicit_reducible]
noncomputable def baseLinear
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    Linear A (Modules X) :=
  Linear.ofRingMorphism (baseCenterHom f)

/-- The relative scalar structure on algebraic-space modules is induced by the
chartwise center map. -/
theorem baseLinear_def
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    baseLinear f = Linear.ofRingMorphism (baseCenterHom f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
