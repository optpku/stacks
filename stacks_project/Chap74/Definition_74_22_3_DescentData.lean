/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap74.Definition_74_22_3_Pseudofunctor

/-!
# Descent data for algebraic spaces over algebraic spaces

The canonical owner is `Pseudofunctor.DescentData` for the pseudofunctor of algebraic-space
slices. The `Chosen` view records explicit pairwise and triple fibre products built from
`pullbackOver`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The chosen fibre product of two morphisms of algebraic spaces, carried by `pullbackOver`. -/
noncomputable def chosenPullbackOver {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ H) (g : G ⟶ H) : ChosenPullback f g where
  pullback := pullbackOver f g H.isSheaf H.representableDiagonal
  p₁ := pullbackOverFst f g H.isSheaf H.representableDiagonal
  p₂ := pullbackOverSnd f g H.isSheaf H.representableDiagonal
  condition := sorry
  isLimit :=
    PullbackCone.IsLimit.mk _
      (fun s ↦ pullbackLift f g s.fst s.snd s.condition) sorry sorry sorry

/-- The first projection of `chosenPullbackOver` is the sheaf fibre-product projection. -/
theorem chosenPullbackOver_p₁ {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ H) (g : G ⟶ H) :
    (chosenPullbackOver f g).p₁ =
      pullbackOverFst f g H.isSheaf H.representableDiagonal := sorry

/-- The second projection of `chosenPullbackOver` is the sheaf fibre-product projection. -/
theorem chosenPullbackOver_p₂ {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ H) (g : G ⟶ H) :
    (chosenPullbackOver f g).p₂ =
      pullbackOverSnd f g H.isSheaf H.representableDiagonal := sorry

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
  (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/-- The category of descent data for a family `f i : Xᵢ i ⟶ X` of morphisms of algebraic
spaces over `S`. -/
abbrev DescentData :=
  (overPseudofunctor S).DescentData f

namespace DescentData

/-- Pulling back an algebraic space over `X` along every `f i` gives canonical descent data. -/
noncomputable def ofObj (V : Over X) : DescentData Xᵢ f :=
  ((overPseudofunctor S).toDescentData f).obj V

/-- The component of `ofObj V` at `i` is the slice pullback of `V` along `f i`. -/
theorem ofObj_obj (V : Over X) (i : I) :
    (ofObj Xᵢ f V).obj i = (overPullback (f i)).obj V := sorry

/-- Two morphisms of algebraic-space descent data are equal when all component maps agree. -/
theorem hom_ext {D E : DescentData Xᵢ f} {a b : D ⟶ E}
    (h : ∀ i, a.hom i = b.hom i) : a = b := sorry

/-- The chosen pairwise fibre product of a family of morphisms of algebraic spaces. -/
noncomputable def overlap (i j : I) : ChosenPullback (f i) (f j) :=
  chosenPullbackOver (f i) (f j)

/-- The first projection of `overlap` is the sheaf fibre-product projection. -/
theorem overlap_p₁ (i j : I) :
    (overlap Xᵢ f i j).p₁ =
      pullbackOverFst (f i) (f j) X.isSheaf X.representableDiagonal := sorry

/-- The second projection of `overlap` is the sheaf fibre-product projection. -/
theorem overlap_p₂ (i j : I) :
    (overlap Xᵢ f i j).p₂ =
      pullbackOverSnd (f i) (f j) X.isSheaf X.representableDiagonal := sorry

/-- The chosen triple fibre product of a family of morphisms of algebraic spaces. -/
noncomputable def tripleOverlap (i j k : I) :
    ChosenPullback₃ (overlap Xᵢ f i j) (overlap Xᵢ f j k) (overlap Xᵢ f i k) :=
  let h₁₂ := overlap Xᵢ f i j
  let h₂₃ := overlap Xᵢ f j k
  let h₁₃ := overlap Xᵢ f i k
  let h := chosenPullbackOver h₁₂.p₂ h₂₃.p₁
  ChosenPullback₃.ofMiddle h₁₂ h₂₃ h₁₃ h
    { f := pullbackLift (f i) (f k) (h.p₁ ≫ h₁₂.p₁) (h.p₂ ≫ h₂₃.p₂) sorry
      f_p₁ := sorry
      f_p₂ := sorry
      f_p := sorry }

/-- The middle square of `tripleOverlap` is the fibre product of the successive overlap
projections. -/
theorem tripleOverlap_chosenPullback (i j k : I) :
    (tripleOverlap Xᵢ f i j k).chosenPullback =
      chosenPullbackOver (overlap Xᵢ f i j).p₂ (overlap Xᵢ f j k).p₁ := sorry

/-- The chosen pairwise- and triple-pullback presentation of algebraic-space descent data. -/
abbrev Chosen
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :=
  (overPseudofunctor S).DescentData' sq sq₃

namespace Chosen

variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

/-- The identity comparison law follows from invertible pairwise comparisons satisfying the
triple-overlap cocycle. -/
theorem ofIso_self
    (V : ∀ i, Over (Xᵢ i))
    (φ : ∀ i j,
      ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : I) :
    Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
      (f i) (𝟙 (Xᵢ i)) (𝟙 (Xᵢ i)) = 𝟙 _ := sorry

/-- Construct a chosen presentation from component spaces, pairwise isomorphisms, and their
triple-overlap cocycle. -/
def ofIso
    (V : ∀ i, Over (Xᵢ i))
    (φ : ∀ i j,
      ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃) :
    Chosen Xᵢ f sq sq₃ where
  obj := V
  hom i j := (φ i j).hom
  pullHom'_hom_self i := ofIso_self Xᵢ f sq sq₃ V φ hφ i
  pullHom'_hom_comp := hφ

/-- The component object of a chosen presentation built by `ofIso` is the supplied space over
`Xᵢ i`. -/
theorem ofIso_obj
    (V : ∀ i, Over (Xᵢ i))
    (φ : ∀ i j,
      ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : I) : (ofIso Xᵢ f sq sq₃ V φ hφ).obj i = V i := sorry

/-- The pairwise comparison map of a chosen presentation built by `ofIso` is the forward map of
the supplied isomorphism. -/
theorem ofIso_hom
    (V : ∀ i, Over (Xᵢ i))
    (φ : ∀ i j,
      ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (V i) ≅
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (V j))
    (hφ : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun a b ↦ (φ a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i j : I) : (ofIso Xᵢ f sq sq₃ V φ hφ).hom i j = (φ i j).hom := sorry

/-- The pairwise comparison morphism of chosen algebraic-space descent data, as an isomorphism
over the chosen overlap. -/
noncomputable def iso (D : Chosen Xᵢ f sq sq₃) (i j : I) :
    ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.obj (D.obj i) ≅
      ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.obj (D.obj j) :=
  asIso (D.hom i j)

/-- The forward map of `iso D i j` is the pairwise comparison map of `D`. -/
theorem iso_hom (D : Chosen Xᵢ f sq sq₃) (i j : I) :
    (iso Xᵢ f sq sq₃ D i j).hom = D.hom i j := sorry

/-- The pairwise comparison isomorphisms satisfy the cocycle condition after pullback to every
chosen triple overlap. -/
theorem cocycle (D : Chosen Xᵢ f sq sq₃) (i j k : I) :
    Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso Xᵢ f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso Xᵢ f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (iso Xᵢ f sq sq₃ D a b).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃ := sorry

/-- A morphism of chosen algebraic-space descent data commutes with every pairwise comparison
isomorphism. -/
theorem hom_comm {D E : Chosen Xᵢ f sq sq₃} (ψ : D ⟶ E) (i j : I) :
    ((overPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.map (ψ.hom i) ≫
        (iso Xᵢ f sq sq₃ E i j).hom =
      (iso Xᵢ f sq sq₃ D i j).hom ≫
        ((overPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.map (ψ.hom j) := sorry

/-- The canonical equivalence from the chosen-overlap presentation to the
representation-independent category of algebraic-space descent data. -/
noncomputable abbrev equivalence : Chosen Xᵢ f sq sq₃ ≌ DescentData Xᵢ f :=
  Pseudofunctor.DescentData'.descentDataEquivalence (overPseudofunctor S) sq sq₃

/-- The chosen-to-canonical equivalence retains every component space over `Xᵢ i`. -/
theorem equivalence_functor_obj_obj (D : Chosen Xᵢ f sq sq₃) (i : I) :
    ((equivalence Xᵢ f sq sq₃).functor.obj D).obj i = D.obj i := sorry

/-- The chosen-to-canonical equivalence retains every component of a descent morphism. -/
theorem equivalence_functor_map_hom {D E : Chosen Xᵢ f sq sq₃}
    (ψ : D ⟶ E) (i : I) :
    ((equivalence Xᵢ f sq sq₃).functor.map ψ).hom i = ψ.hom i := sorry

end Chosen

end DescentData

end AlgebraicGeometry.AlgebraicSpace
