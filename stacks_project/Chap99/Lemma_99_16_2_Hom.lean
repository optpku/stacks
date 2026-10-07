module

public import stacks_project.Chap99.Lemma_99_3_8_Yoneda
public import stacks_project.Chap99.Lemma_99_16_1_Hom
public import stacks_project.Chap99.Lemma_99_16_1_Pullback

/-!
# Self-Hom functor of derived pullbacks over `Y`

On algebraic spaces over `Y`, the assignment `V ↦ Hom_{𝒪_{X_V}}(E_V, E_V)` is a
contravariant functor. Its restriction to schemes over `Y` is the comparison
target of `IsAffineFinitePresentationOver`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction of a derived self-Hom after base change along a morphism of
algebraic spaces over `Y`. -/
def selfHomRestrict (f : X ⟶ Y) (E : ModuleDerived X) {σ τ : Over Y} (h : τ ⟶ σ)
    (u : baseChangePullback f σ.hom E ⟶ baseChangePullback f σ.hom E) :
    baseChangePullback f τ.hom E ⟶ baseChangePullback f τ.hom E :=
  baseChangeHom f E E h.left (Over.w h) u

/-- The functor `V ↦ Hom_{𝒪_{X_V}}(E_V, E_V)` on algebraic spaces over `Y`. -/
def selfHomFunctorOver (f : X ⟶ Y) (E : ModuleDerived X) :
    (Over Y)ᵒᵖ ⥤ Type (u + 1) where
  obj σ :=
    baseChangePullback f σ.unop.hom E ⟶ baseChangePullback f σ.unop.hom E
  map {σ τ} h := TypeCat.ofHom (selfHomRestrict f E h.unop)
  map_id := sorry
  map_comp := sorry

/-- Evaluating `selfHomFunctorOver` at an algebraic space over `Y` yields derived
self-Hom of the base-changed complex. -/
theorem selfHomFunctorOver_obj (f : X ⟶ Y) (E : ModuleDerived X) (σ : Over Y) :
    (selfHomFunctorOver f E).obj (op σ) =
      (baseChangePullback f σ.hom E ⟶ baseChangePullback f σ.hom E) :=
  sorry

/-- `selfHomFunctorOver` acts on morphisms of algebraic spaces over `Y` by
`selfHomRestrict`. -/
theorem selfHomFunctorOver_map (f : X ⟶ Y) (E : ModuleDerived X)
    {σ τ : Over Y} (h : τ ⟶ σ) :
    (selfHomFunctorOver f E).map h.op = TypeCat.ofHom (selfHomRestrict f E h) :=
  sorry

/-- The restriction of `selfHomFunctorOver` to schemes over `Y`. -/
def selfHomFunctor (f : X ⟶ Y) (E : ModuleDerived X) :
    (SchemeOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  SchemeOver.toOver.op ⋙ selfHomFunctorOver f E

/-- Evaluating `selfHomFunctor` at a scheme over `Y` yields derived self-Hom of
the base-changed complex. -/
theorem selfHomFunctor_obj (f : X ⟶ Y) (E : ModuleDerived X) (σ : SchemeOver Y) :
    (selfHomFunctor f E).obj (op σ) =
      (baseChangePullback f σ.hom E ⟶ baseChangePullback f σ.hom E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
