/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import ReasLib.AlgebraicGeometry.Scheme.Over.Pseudofunctor

/-!
# Descent data for schemes over schemes

The canonical owner is `Pseudofunctor.DescentData` for the pseudofunctor of scheme slices.
The `Chosen` view records explicit pairwise and triple pullbacks.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

variable {I : Type v} {S : Scheme.{u}}

/-- The category of descent data for a family `f i : X i ⟶ S` of scheme morphisms. -/
abbrev DescentData (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S) :=
  overPseudofunctor.DescentData f

namespace DescentData

variable (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)

/-- Pulling back a scheme over `S` along every `f i` gives canonical descent data. -/
noncomputable def ofObj (V : Over S) : DescentData X f :=
  (overPseudofunctor.toDescentData f).obj V

/-- The component of `ofObj V` at `i` is the pullback of `V` along `f i`. -/
theorem ofObj_obj (V : Over S) (i : I) :
    (ofObj X f V).obj i = (Over.pullback (f i)).obj V := sorry

/-- Two morphisms of scheme descent data are equal when all component maps agree. -/
theorem hom_ext {D E : DescentData X f} {a b : D ⟶ E}
    (h : ∀ i, a.hom i = b.hom i) : a = b := sorry

/-- The chosen pairwise- and triple-pullback presentation of scheme descent data. -/
abbrev Chosen
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :=
  overPseudofunctor.DescentData' sq sq₃

namespace Chosen

variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

/-- The identity comparison law follows from invertible pairwise comparisons satisfying the
triple-overlap cocycle. -/
theorem ofIso_self
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (overPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : I) :
    Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
      (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := sorry

/-- Construct a chosen presentation from component schemes, pairwise isomorphisms, and their
triple-overlap cocycle. -/
def ofIso
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (overPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃) :
    Chosen X f sq sq₃ where
  obj := V
  hom i j := (φ i j).hom
  pullHom'_hom_self i := ofIso_self X f sq sq₃ V φ hφ i
  pullHom'_hom_comp := hφ

/-- The component object of a chosen presentation built by `ofIso` is the supplied scheme over
`X i`. -/
theorem ofIso_obj
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (overPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : I) : (ofIso X f sq sq₃ V φ hφ).obj i = V i := sorry

/-- The pairwise comparison map of a chosen presentation built by `ofIso` is the forward map of
the supplied isomorphism. -/
theorem ofIso_hom
    (V : ∀ i, Over (X i))
    (φ : ∀ i j,
      (overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        (overPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i j : I) : (ofIso X f sq sq₃ V φ hφ).hom i j = (φ i j).hom := sorry

/-- The pairwise comparison morphism of chosen scheme descent data, as an isomorphism over the
chosen overlap. -/
noncomputable def iso (D : Chosen X f sq sq₃) (i j : I) :
    (overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (D.obj i) ≅
      (overPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (D.obj j) :=
  asIso (D.hom i j)

/-- The forward map of `iso D i j` is the pairwise comparison map of `D`. -/
theorem iso_hom (D : Chosen X f sq sq₃) (i j : I) :
    (iso X f sq sq₃ D i j).hom = D.hom i j := sorry

/-- The pairwise comparison isomorphisms satisfy the cocycle condition after pullback to every
chosen triple overlap. -/
theorem cocycle (D : Chosen X f sq sq₃) (i j k : I) :
    Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso X f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso X f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso X f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃ := sorry

/-- A morphism of chosen scheme descent data commutes with every pairwise comparison
isomorphism. -/
theorem hom_comm {D E : Chosen X f sq sq₃} (ψ : D ⟶ E) (i j : I) :
    (overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.map (ψ.hom i) ≫
        (iso X f sq sq₃ E i j).hom =
      (iso X f sq sq₃ D i j).hom ≫
        (overPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.map (ψ.hom j) := sorry

/-- The canonical equivalence from the chosen-overlap presentation to the
representation-independent category of scheme descent data. -/
noncomputable abbrev equivalence : Chosen X f sq sq₃ ≌ DescentData X f :=
  Pseudofunctor.DescentData'.descentDataEquivalence overPseudofunctor sq sq₃

/-- The chosen-to-canonical equivalence retains every component scheme over `X i`. -/
theorem equivalence_functor_obj_obj (D : Chosen X f sq sq₃) (i : I) :
    ((equivalence X f sq sq₃).functor.obj D).obj i = D.obj i := sorry

/-- The chosen-to-canonical equivalence retains every component of a descent morphism. -/
theorem equivalence_functor_map_hom {D E : Chosen X f sq sq₃}
    (ψ : D ⟶ E) (i : I) :
    ((equivalence X f sq sq₃).functor.map ψ).hom i = ψ.hom i := sorry

end Chosen

end DescentData

end AlgebraicGeometry.Scheme
