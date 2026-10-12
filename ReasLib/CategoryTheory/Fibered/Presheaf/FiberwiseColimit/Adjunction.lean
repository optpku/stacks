/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf.FiberwiseColimit
public import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Tactic.CrossRefAttribute

/-!
# The fiberwise-colimit adjunction

Fiberwise colimit is left adjoint to precomposition with the opposite projection.  The two maps
of the Hom equivalence are given explicitly by the colimit injections and the colimit descent
maps; only their naturality and inverse laws are deferred.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v wX vX a b

namespace CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable (A : Type a) [Category.{b} A]
variable [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A]

/-- Precomposition of base presheaves with the opposite fibered projection. -/
@[stacks 08PE "precomposition along a fibered projection"]
abbrev precompose : (Cᵒᵖ ⥤ A) ⥤ (X.totalᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft X.totalᵒᵖ Cᵒᵖ A).obj X.p.op

/-- The component of the adjunction map from a fiberwise-colimit morphism to a morphism after
precomposition with the projection. -/
@[stacks 08PE "fiberwise-colimit adjunction forward component"]
noncomputable def toPrecomposeApp
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (α : (functor X A).obj F ⟶ G) (x : X.totalᵒᵖ) :
    F.obj x ⟶ (precompose X A).obj G |>.obj x :=
  colimit.ι (restrict X A F (X.p.obj x.unop))
      (op (Functor.Fiber.mk (p := X.p) (a := x.unop) rfl)) ≫
    α.app (op (X.p.obj x.unop))

/-- Naturality of `toPrecomposeApp` in the total-category object. -/
@[stacks 08PE "fiberwise-colimit adjunction forward naturality"]
theorem toPrecompose_naturality
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (α : (functor X A).obj F ⟶ G) :
    ∀ {x y : X.totalᵒᵖ} (f : x ⟶ y),
      F.map f ≫ toPrecomposeApp X A F G α y =
        toPrecomposeApp X A F G α x ≫ ((precompose X A).obj G).map f := sorry

/-- The adjunction map from a fiberwise-colimit morphism to a morphism after precomposition. -/
@[stacks 08PE "fiberwise-colimit adjunction forward map"]
noncomputable def toPrecompose
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A) :
    ((functor X A).obj F ⟶ G) → (F ⟶ (precompose X A).obj G) :=
  fun α =>
    { app := toPrecomposeApp X A F G α
      naturality := fun {_ _} f ↦ toPrecompose_naturality X A F G α f }

/-- The leg of the cocone induced by a morphism into a precomposed base presheaf. -/
@[stacks 08PE "fiberwise-colimit adjunction descent leg"]
noncomputable def fromPrecomposeCoconeApp
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (β : F ⟶ (precompose X A).obj G) (V : C)
    (x : (X.p.Fiber V)ᵒᵖ) :
    (restrict X A F V).obj x ⟶ G.obj (op V) :=
  β.app (op x.unop.1) ≫
    G.map (eqToHom (congrArg op x.unop.2))

/-- Naturality of the cocone legs induced by a morphism into a precomposed presheaf. -/
@[stacks 08PE "fiberwise-colimit adjunction descent naturality"]
theorem fromPrecomposeCocone_naturality
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (β : F ⟶ (precompose X A).obj G) (V : C) :
    ∀ {x y : (X.p.Fiber V)ᵒᵖ} (f : x ⟶ y),
      (restrict X A F V).map f ≫ fromPrecomposeCoconeApp X A F G β V y =
        fromPrecomposeCoconeApp X A F G β V x ≫
          ((Functor.const (X.p.Fiber V)ᵒᵖ).obj (G.obj (op V))).map f := sorry

/-- The cocone over one fiber induced by a morphism into a precomposed base presheaf. -/
@[stacks 08PE "fiberwise-colimit adjunction descent cocone"]
noncomputable def fromPrecomposeCocone
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (β : F ⟶ (precompose X A).obj G) (V : C) :
    Cocone (restrict X A F V) where
  pt := G.obj (op V)
  ι :=
    { app := fromPrecomposeCoconeApp X A F G β V
      naturality := fun {_ _} f ↦ fromPrecomposeCocone_naturality X A F G β V f }

/-- The component on the base of the morphism descended from a precomposed-presheaf map. -/
@[stacks 08PE "fiberwise-colimit adjunction descended component"]
noncomputable def fromPrecomposeApp
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (β : F ⟶ (precompose X A).obj G) (V : Cᵒᵖ) :
    ((functor X A).obj F).obj V ⟶ G.obj V :=
  colimit.desc (restrict X A F V.unop)
    (fromPrecomposeCocone X A F G β V.unop)

/-- Naturality on the base of the morphism descended from a precomposed-presheaf map. -/
@[stacks 08PE "fiberwise-colimit adjunction descended naturality"]
theorem fromPrecompose_naturality
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (β : F ⟶ (precompose X A).obj G) :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
      ((functor X A).obj F).map f ≫ fromPrecomposeApp X A F G β V =
        fromPrecomposeApp X A F G β U ≫ G.map f := sorry

/-- The morphism of base presheaves descended from a morphism into a precomposed presheaf. -/
@[stacks 08PE "fiberwise-colimit adjunction descended map"]
noncomputable def fromPrecompose
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A) :
    (F ⟶ (precompose X A).obj G) → ((functor X A).obj F ⟶ G) :=
  fun β =>
    { app := fromPrecomposeApp X A F G β
      naturality := fun {_ _} f ↦ fromPrecompose_naturality X A F G β f }

/-- Descending after applying the forward adjunction map recovers the original morphism. -/
@[stacks 08PE "fiberwise-colimit adjunction left inverse"]
theorem fromPrecompose_toPrecompose
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (α : (functor X A).obj F ⟶ G) :
    fromPrecompose X A F G (toPrecompose X A F G α) = α := sorry

/-- Applying the forward adjunction map after descent recovers the original morphism. -/
@[stacks 08PE "fiberwise-colimit adjunction right inverse"]
theorem toPrecompose_fromPrecompose
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A)
    (β : F ⟶ (precompose X A).obj G) :
    toPrecompose X A F G (fromPrecompose X A F G β) = β := sorry

/-- The Hom equivalence expressing the fiberwise-colimit adjunction. -/
@[stacks 08PE "fiberwise-colimit Hom equivalence"]
noncomputable def homEquiv
    (F : X.totalᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ A) :
    ((functor X A).obj F ⟶ G) ≃ (F ⟶ (precompose X A).obj G) where
  toFun := toPrecompose X A F G
  invFun := fromPrecompose X A F G
  left_inv := fromPrecompose_toPrecompose X A F G
  right_inv := toPrecompose_fromPrecompose X A F G

/-- Naturality of the inverse Hom equivalence in the source presheaf. -/
@[stacks 08PE "fiberwise-colimit Hom equivalence source naturality"]
theorem homEquiv_naturality_left_symm
    {F F' : X.totalᵒᵖ ⥤ A} (G : Cᵒᵖ ⥤ A)
    (f : F ⟶ F') (g : F' ⟶ (precompose X A).obj G) :
    (homEquiv X A F G).symm (f ≫ g) =
      (functor X A).map f ≫ (homEquiv X A F' G).symm g := sorry

/-- Naturality of the Hom equivalence in the target presheaf. -/
@[stacks 08PE "fiberwise-colimit Hom equivalence target naturality"]
theorem homEquiv_naturality_right
    (F : X.totalᵒᵖ ⥤ A) {G G' : Cᵒᵖ ⥤ A}
    (f : (functor X A).obj F ⟶ G) (g : G ⟶ G') :
    homEquiv X A F G' (f ≫ g) =
      homEquiv X A F G f ≫ (precompose X A).map g := sorry

/-- The core Hom-equivalence data for the fiberwise-colimit adjunction. -/
@[stacks 08PE "fiberwise-colimit adjunction core"]
noncomputable def coreHomEquiv :
    Adjunction.CoreHomEquiv (functor X A) (precompose X A) where
  homEquiv := homEquiv X A
  homEquiv_naturality_left_symm :=
    fun {F' F G} f g ↦ homEquiv_naturality_left_symm X A G f g
  homEquiv_naturality_right :=
    fun {F G G'} f g ↦ homEquiv_naturality_right X A F f g

/-- Fiberwise colimit is left adjoint to precomposition with the opposite projection. -/
@[stacks 08PE "fiberwise-colimit adjunction"]
noncomputable def adjunction : functor X A ⊣ precompose X A :=
  Adjunction.mkOfHomEquiv (coreHomEquiv X A)

-- The morphism and cocone data are explicit.  The deferred axioms below occur only in their
-- naturality, inverse, and adjunction coherence proofs.

end CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit
