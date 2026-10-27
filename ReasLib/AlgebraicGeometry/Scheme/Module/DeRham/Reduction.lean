/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Terms
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules.DeRham

universe u

namespace AlgebraicGeometry.Scheme.Modules.DeRham.Reduction

variable {A : Type u} [CommRing A] {Y Z : Scheme.{u}}
variable (f : Y ⟶ Spec (.of A)) (j : Z ⟶ Y)
variable (M : Y.Modules) (N : Z.Modules)

/-- The canonical comparison on relative one-forms sends db to d(j*b).
This morphism is fixed by the universal derivation, not chosen as an isomorphism. -/
noncomputable def differentialComparison :
    (Scheme.Modules.pullback j).obj (oneForms f) ⟶ oneForms (j ≫ f) :=
  RingedSpace.Hom.Differentials.comparison
    (f := j.toShHom) (g := 𝟙 (Spec (.of A)).toRingedSpace)
    (h := f.toShHom) (h' := (j ≫ f).toShHom)
    ({ w := (Category.comp_id (j.toShHom ≫ f.toShHom)).symm } :
      CommSq j.toShHom (j.toShHom ≫ f.toShHom) f.toShHom (𝟙 _))

/-- Tensor pullback followed by the specified coefficient map and the canonical
relative differential comparison. There is no independent choice of the form map. -/
noncomputable def tensorComparison
    (i : (Scheme.Modules.pullback j).obj M ⟶ N) :
    (Scheme.Modules.pullback j).obj (oneFormTensor f M) ⟶
      oneFormTensor (j ≫ f) N :=
  (Scheme.Modules.pullbackTensorIso j M (oneForms f)).hom ≫
    (i ⊗ₘ differentialComparison f j)

/-- The actual quotient/restriction map of coefficients, as a map to the
pushforward of the pulled module. The pullback includes extension of scalars. -/
noncomputable def coefficientAdjoint
    (i : (Scheme.Modules.pullback j).obj M ⟶ N) :
    M ⟶ (Scheme.Modules.pushforward j).obj N :=
  (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv M N i

/-- The corresponding quotient/restriction map on coefficients tensored with
one-forms, induced functorially by the same coefficient map. -/
noncomputable def tensorAdjoint
    (i : (Scheme.Modules.pullback j).obj M ⟶ N) :
    oneFormTensor f M ⟶ (Scheme.Modules.pushforward j).obj (oneFormTensor (j ≫ f) N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _
    (tensorComparison f j M N i)

/-- The given A-linear sheaf connection evaluated on arbitrary open sections. -/
noncomputable def connectionOnOpen
    (nabla : asBaseSheaf f M ⟶ asBaseSheaf f (oneFormTensor f M))
    (U : Y.Opens) : Γ(M, U) →+ Γ(oneFormTensor f M, U) :=
  (nabla.hom.app (op U)).hom.toAddMonoidHom

/-- Horizontality of a coefficient comparison is the actual commutative
reduction square on sections. In particular the connection on the source
descends through the module quotient rather than a false inverse-image isomorphism. -/
def IsHorizontal
    (nabla : asBaseSheaf f M ⟶ asBaseSheaf f (oneFormTensor f M))
    (nabla' : asBaseSheaf (j ≫ f) N ⟶ asBaseSheaf (j ≫ f) (oneFormTensor (j ≫ f) N))
    (i : (Scheme.Modules.pullback j).obj M ⟶ N) : Prop :=
  ∀ (U : Y.Opens) (m : Γ(M, U)),
    connectionOnOpen (j ≫ f) N nabla' (j ⁻¹ᵁ U)
        ((coefficientAdjoint j M N i).app U m) =
      (tensorAdjoint f j M N i).app U (connectionOnOpen f M nabla U m)

/-- Horizontality fixes the quotient connection on the image of every original
section using the induced tensor/differential map. -/
theorem isHorizontal_on_sections
    (nabla : asBaseSheaf f M ⟶ asBaseSheaf f (oneFormTensor f M))
    (nabla' : asBaseSheaf (j ≫ f) N ⟶ asBaseSheaf (j ≫ f) (oneFormTensor (j ≫ f) N))
    (i : (Scheme.Modules.pullback j).obj M ⟶ N)
    (h : IsHorizontal f j M N nabla nabla' i)
    (U : Y.Opens) (m : Γ(M, U)) :
    connectionOnOpen (j ≫ f) N nabla' (j ⁻¹ᵁ U)
        ((coefficientAdjoint j M N i).app U m) =
      (tensorAdjoint f j M N i).app U (connectionOnOpen f M nabla U m) := h U m

end AlgebraicGeometry.Scheme.Modules.DeRham.Reduction
