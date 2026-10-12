/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.Algebra.Category.ModuleCat.Bimod
public import ReasLib.Algebra.Module.Bimodule.RelativeTensor.Map

/-!
# Concrete relative tensors as categorical bimodule tensors

This file compares the explicit quotient presentation of an ordinary relative tensor product
with Mathlib's coequalizer presentation of the tensor product of bimodule objects in
`ModuleCat`.  It is deliberately restricted to one universe, as is the monoidal structure on
`ModuleCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory RelativeTensor TensorProduct

noncomputable section

universe u

namespace Module.Bimodule.RelativeTensor

variable {R A B M N : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
variable [IsScalarTower R Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]

/-- The canonical projection from the ground-ring tensor product to Mathlib's categorical
balanced tensor product. -/
noncomputable def tensorBimodMk :
    (toRightModule (R := R) (A := A) M).X ⊗
        (toBimod (R := R) (A := A) (B := B) N).X ⟶
      ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).X :=
  coequalizer.π
    ((toRightModule (R := R) (A := A) M).actRight ▷
      (toBimod (R := R) (A := A) (B := B) N).X)
    ((α_ _ _ _).hom ≫
      ((toRightModule (R := R) (A := A) M).X ◁
        (toBimod (R := R) (A := A) (B := B) N).actLeft))

namespace FromTensorBimod

/-- The concrete quotient map coequalizes the two categorical middle-action maps. -/
theorem condition :
    ((toRightModule (R := R) (A := A) M).actRight ▷
        (toBimod (R := R) (A := A) (B := B) N).X) ≫
        ModuleCat.ofHom (mk (R := R) (A := A) (M := M) (N := N)) =
      ((α_ _ _ _).hom ≫
        ((toRightModule (R := R) (A := A) M).X ◁
          (toBimod (R := R) (A := A) (B := B) N).actLeft)) ≫
        ModuleCat.ofHom (mk (R := R) (A := A) (M := M) (N := N)) := sorry

/-- The underlying map from the categorical coequalizer to the explicit relative tensor
quotient. -/
noncomputable def moduleHom :
    ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).X ⟶
      (toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N)).X :=
  coequalizer.desc (ModuleCat.ofHom (mk (R := R) (A := A) (M := M) (N := N)))
    (condition (R := R) (A := A) (B := B) (M := M) (N := N))

/-- The map from the categorical tensor product to the explicit quotient respects the trivial
left action. -/
theorem left_act_hom :
    ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).actLeft ≫
        moduleHom (R := R) (A := A) (B := B) (M := M) (N := N) =
      ((Mon.trivial (ModuleCat R)).X ◁
        moduleHom (R := R) (A := A) (B := B) (M := M) (N := N)) ≫
        (toRightModule (R := R) (A := B)
          (M ⊗ᵣ[R, A] N)).actLeft := sorry

/-- The map from the categorical tensor product to the explicit quotient respects the right
`B`-action. -/
theorem right_act_hom :
    ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).actRight ≫
        moduleHom (R := R) (A := A) (B := B) (M := M) (N := N) =
      (moduleHom (R := R) (A := A) (B := B) (M := M) (N := N) ▷
        (algebraMon (R := R) B).X) ≫
        (toRightModule (R := R) (A := B)
          (M ⊗ᵣ[R, A] N)).actRight := sorry

end FromTensorBimod

/-- The categorical balanced tensor product maps canonically to the explicit relative tensor
quotient. -/
noncomputable def fromTensorBimod :
    (toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N) ⟶
      toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N) where
  hom := FromTensorBimod.moduleHom
  left_act_hom := FromTensorBimod.left_act_hom
  right_act_hom := FromTensorBimod.right_act_hom

/-- The categorical projection followed by `fromTensorBimod` is the explicit quotient map. -/
@[simp]
theorem tensorBimodMk_fromTensorBimod :
    tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N) ≫
        (fromTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N)).hom =
      ModuleCat.ofHom (mk (R := R) (A := A) (M := M) (N := N)) := sorry

/-- Mapping a categorical pure tensor to the explicit quotient gives its relative tensor class. -/
@[simp]
theorem fromTensorBimod_tmul (m : M) (n : N) :
    (fromTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N)).hom
        (tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)
          (m ⊗ₜ[R] n)) =
      tmul (R := R) (A := A) m n := sorry

namespace ToTensorBimod

/-- The bilinear pairing sending `(m, n)` to the categorical class of `m ⊗ n`. -/
noncomputable def pairing :
    M →ₗ[R] N →ₗ[R]
      ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).X :=
  TensorProduct.curry
    (tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)).hom

/-- The curried categorical pairing evaluates by applying the coequalizer projection to a
pure ground-ring tensor. -/
@[simp]
theorem pairing_apply (m : M) (n : N) :
    pairing (R := R) (A := A) (B := B) (M := M) (N := N) m n =
      tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)
        (m ⊗ₜ[R] n) := sorry

/-- The categorical pure-tensor pairing is balanced over the middle algebra `A`. -/
theorem pairing_balanced :
    IsBalanced (R := R) (A := A) (M := M) (N := N)
      (pairing (R := R) (A := A) (B := B) (M := M) (N := N)) := sorry

/-- The underlying `R`-linear map from the explicit quotient to the categorical coequalizer. -/
noncomputable def linearMap :
    (M ⊗ᵣ[R, A] N) →ₗ[R]
      ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).X :=
  lift (R := R) (A := A) (M := M) (N := N)
    (pairing (R := R) (A := A) (B := B) (M := M) (N := N))
    (pairing_balanced (R := R) (A := A) (B := B) (M := M) (N := N))

/-- The underlying `ModuleCat` map from the explicit quotient to the categorical tensor. -/
noncomputable def moduleHom :
    (toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N)).X ⟶
      ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)).X :=
  ModuleCat.ofHom (linearMap (R := R) (A := A) (B := B) (M := M) (N := N))

/-- The map from the explicit quotient to the categorical tensor respects the trivial left
action. -/
theorem left_act_hom :
    (toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N)).actLeft ≫
        moduleHom (R := R) (A := A) (B := B) (M := M) (N := N) =
      ((Mon.trivial (ModuleCat R)).X ◁
        moduleHom (R := R) (A := A) (B := B) (M := M) (N := N)) ≫
        ((toRightModule (R := R) (A := A) M).tensorBimod
          (toBimod (R := R) (A := A) (B := B) N)).actLeft := sorry

/-- The map from the explicit quotient to the categorical tensor respects the right `B`-action. -/
theorem right_act_hom :
    (toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N)).actRight ≫
        moduleHom (R := R) (A := A) (B := B) (M := M) (N := N) =
      (moduleHom (R := R) (A := A) (B := B) (M := M) (N := N) ▷
        (algebraMon (R := R) B).X) ≫
        ((toRightModule (R := R) (A := A) M).tensorBimod
          (toBimod (R := R) (A := A) (B := B) N)).actRight := sorry

end ToTensorBimod

/-- The explicit relative tensor quotient maps canonically to Mathlib's categorical balanced
tensor product. -/
noncomputable def toTensorBimod :
    toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N) ⟶
      (toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N) where
  hom := ToTensorBimod.moduleHom
  left_act_hom := ToTensorBimod.left_act_hom
  right_act_hom := ToTensorBimod.right_act_hom

/-- Mapping an explicit pure relative tensor to the categorical tensor gives its coequalizer
class. -/
@[simp]
theorem toTensorBimod_tmul (m : M) (n : N) :
    (toTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N)).hom
        (tmul (R := R) (A := A) m n) =
      tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)
        (m ⊗ₜ[R] n) := sorry

/-- Mapping from the categorical tensor to the explicit quotient and back is the identity. -/
@[simp]
theorem fromTensorBimod_toTensorBimod :
    fromTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N) ≫
        toTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N) =
      𝟙 ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)) := sorry

/-- Mapping from the explicit quotient to the categorical tensor and back is the identity. -/
@[simp]
theorem toTensorBimod_fromTensorBimod :
    toTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N) ≫
        fromTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N) =
      𝟙 (toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N)) := sorry

/-- The explicit quotient and Mathlib's categorical balanced tensor product are canonically
isomorphic as right `B`-modules. -/
@[stacks 09LN "ordinary and categorical relative tensor products"]
noncomputable def tensorBimodIso :
    (toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N) ≅
      toRightModule (R := R) (A := B)
        (M ⊗ᵣ[R, A] N) where
  hom := fromTensorBimod
  inv := toTensorBimod
  hom_inv_id := fromTensorBimod_toTensorBimod
  inv_hom_id := toTensorBimod_fromTensorBimod

/-- The forward map of `tensorBimodIso` is the canonical map to the explicit quotient. -/
@[simp]
theorem tensorBimodIso_hom :
    (tensorBimodIso (R := R) (A := A) (B := B) (M := M) (N := N)).hom =
      fromTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N) := sorry

/-- The inverse map of `tensorBimodIso` is the canonical map to the categorical tensor. -/
@[simp]
theorem tensorBimodIso_inv :
    (tensorBimodIso (R := R) (A := A) (B := B) (M := M) (N := N)).inv =
      toTensorBimod (R := R) (A := A) (B := B) (M := M) (N := N) := sorry

/-- The forward map of `tensorBimodIso` sends a categorical pure tensor to its explicit
relative tensor class. -/
@[simp]
theorem tensorBimodIso_hom_tmul (m : M) (n : N) :
    (tensorBimodIso (R := R) (A := A) (B := B) (M := M) (N := N)).hom.hom
        (tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)
          (m ⊗ₜ[R] n)) =
      tmul (R := R) (A := A) m n := sorry

/-- The inverse map of `tensorBimodIso` sends an explicit pure relative tensor to its
categorical coequalizer class. -/
@[simp]
theorem tensorBimodIso_inv_tmul (m : M) (n : N) :
    (tensorBimodIso (R := R) (A := A) (B := B) (M := M) (N := N)).inv.hom
        (tmul (R := R) (A := A) m n) =
      tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)
        (m ⊗ₜ[R] n) := sorry

section Naturality

variable {M' N' : Type u}
variable [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M']
variable [IsScalarTower R Aᵐᵒᵖ M']
variable [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
variable [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N']
variable [SMulCommClass A Bᵐᵒᵖ N']

/-- The simultaneous categorical tensor map induced by maps in both ordinary module factors. -/
@[stacks 09LN "functoriality of categorical relative tensor products"]
noncomputable def tensorBimodMap (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    (toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N) ⟶
      (toRightModule (R := R) (A := A) M').tensorBimod
        (toBimod (R := R) (A := A) (B := B) N') :=
  Bimod.whiskerRight (ToRightModule.map (R := R) f)
      (toBimod (R := R) (A := A) (B := B) N) ≫
    Bimod.whiskerLeft (toRightModule (R := R) (A := A) M')
      (Hom.toBimod g)

/-- The simultaneous categorical tensor map evaluates componentwise on pure tensors. -/
@[simp]
theorem tensorBimodMap_tmul (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (m : M) (n : N) :
    (tensorBimodMap (R := R) (A := A) (B := B) f g).hom
        (tensorBimodMk (R := R) (A := A) (B := B) (M := M) (N := N)
          (m ⊗ₜ[R] n)) =
      tensorBimodMk (R := R) (A := A) (B := B) (M := M') (N := N')
        (f m ⊗ₜ[R] g n) := sorry

/-- The simultaneous categorical tensor map preserves identity morphisms. -/
@[simp]
theorem tensorBimodMap_id :
    tensorBimodMap (R := R) (A := A) (B := B)
        (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M)
        (Hom.id (R := R) (A := A) (B := B) (N := N)) =
      𝟙 ((toRightModule (R := R) (A := A) M).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N)) := sorry

/-- With the first factor fixed, the simultaneous categorical tensor map is left whiskering. -/
@[simp]
theorem tensorBimodMap_id_left
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    tensorBimodMap (R := R) (A := A) (B := B)
        (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) g =
      Bimod.whiskerLeft (toRightModule (R := R) (A := A) M) (Hom.toBimod g) := sorry

/-- With the bimodule factor fixed, the simultaneous categorical tensor map is right
whiskering. -/
@[simp]
theorem tensorBimodMap_id_right (f : M →ₗ[Aᵐᵒᵖ] M') :
    tensorBimodMap (R := R) (A := A) (B := B) f
        (Hom.id (R := R) (A := A) (B := B) (N := N)) =
      Bimod.whiskerRight (ToRightModule.map (R := R) f)
        (toBimod (R := R) (A := A) (B := B) N) := sorry

/-- Successive simultaneous categorical tensor maps compose componentwise. -/
theorem tensorBimodMap_comp
    {M'' N'' : Type u}
    [AddCommGroup M''] [Module R M''] [Module Aᵐᵒᵖ M''] [IsScalarTower R Aᵐᵒᵖ M'']
    [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    (f : M →ₗ[Aᵐᵒᵖ] M') (f' : M' →ₗ[Aᵐᵒᵖ] M'')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g' : Hom (R := R) (A := A) (B := B) (N := N') (N' := N'')) :
    tensorBimodMap (R := R) (A := A) (B := B) (f'.comp f)
        (Hom.comp g' g) =
      tensorBimodMap (R := R) (A := A) (B := B) f g ≫
        tensorBimodMap (R := R) (A := A) (B := B) f' g' := sorry

/-- The forward concrete-categorical relative tensor isomorphism is natural simultaneously in
both ordinary module factors. -/
@[reassoc]
theorem tensorBimodIso_hom_naturality (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    tensorBimodMap (R := R) (A := A) (B := B) f g ≫
        (tensorBimodIso (R := R) (A := A) (B := B) (M := M') (N := N')).hom =
      (tensorBimodIso (R := R) (A := A) (B := B) (M := M) (N := N)).hom ≫
        ToRightModule.map (R := R)
          (map (R := R) (A := A) (B := B) f g) := sorry

/-- The inverse concrete-categorical relative tensor isomorphism is natural simultaneously in
both ordinary module factors. -/
@[reassoc]
theorem tensorBimodIso_inv_naturality (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    ToRightModule.map (R := R)
        (map (R := R) (A := A) (B := B) f g) ≫
        (tensorBimodIso (R := R) (A := A) (B := B) (M := M') (N := N')).inv =
      (tensorBimodIso (R := R) (A := A) (B := B) (M := M) (N := N)).inv ≫
        tensorBimodMap (R := R) (A := A) (B := B) f g := sorry

end Naturality

end Module.Bimodule.RelativeTensor

end
