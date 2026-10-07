module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap74.Definition_74_3_1_Pseudofunctor

/-!
# Quasi-coherent descent data on algebraic spaces

A family of morphisms of algebraic spaces determines a category of module-sheaf descent data.
Quasi-coherent descent data is the full subcategory on componentwise quasi-coherent objects,
with a chosen-overlap presentation recovering the pairwise comparison isomorphisms and the
cocycle condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}
  (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/-- The property that every component of canonical module descent data is quasi-coherent. -/
abbrev descentProperty :
    ObjectProperty ((Modules.descentPseudofunctor S).DescentData f) :=
  fun D ↦ ∀ i, (D.obj i).IsQuasicoherent

/-- Componentwise characterization of the quasi-coherence property on canonical descent data. -/
theorem descentProperty_iff (D : (Modules.descentPseudofunctor S).DescentData f) :
    descentProperty Xᵢ f D ↔ ∀ i, (D.obj i).IsQuasicoherent := sorry

/-- Componentwise quasi-coherence is invariant under isomorphisms of descent data. -/
instance descentPropertyIsClosedUnderIsomorphisms :
    (descentProperty Xᵢ f).IsClosedUnderIsomorphisms := sorry

/-- Quasi-coherent descent data for the family `f : ∀ i, Xᵢ i ⟶ X` of morphisms of algebraic
spaces over `S`. -/
abbrev DescentData :=
  (descentProperty Xᵢ f).FullSubcategory

namespace DescentData

/-- Regard canonical module descent data with quasi-coherent components as quasi-coherent
descent data. -/
def of (D : (Modules.descentPseudofunctor S).DescentData f)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) : DescentData Xᵢ f :=
  ⟨D, hD⟩

/-- The underlying canonical descent datum of `of` is the supplied datum. -/
theorem of_obj (D : (Modules.descentPseudofunctor S).DescentData f)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) :
    (of Xᵢ f D hD).obj = D := sorry

/-- Every component of quasi-coherent descent data is quasi-coherent. -/
theorem localIsQuasicoherent (D : DescentData Xᵢ f) (i : I) :
    (D.obj.obj i).IsQuasicoherent := sorry

/-- Two morphisms of quasi-coherent descent data are equal when all component maps agree. -/
theorem homExt {D E : DescentData Xᵢ f} {a b : D ⟶ E}
    (h : ∀ i, a.hom.hom i = b.hom.hom i) : a = b := sorry

/-- The canonical pairwise fibre product of a family of morphisms of algebraic spaces. -/
noncomputable def overlap (i j : I) : ChosenPullback (f i) (f j) :=
  ChosenPullback.ofHasPullback (f i) (f j)

/-- The first projection of `overlap` is the canonical fibre-product projection. -/
theorem overlap_p₁ (i j : I) :
    (overlap Xᵢ f i j).p₁ = pullback.fst (f i) (f j) := sorry

/-- The second projection of `overlap` is the canonical fibre-product projection. -/
theorem overlap_p₂ (i j : I) :
    (overlap Xᵢ f i j).p₂ = pullback.snd (f i) (f j) := sorry

/-- The canonical triple fibre product of a family of morphisms of algebraic spaces. -/
noncomputable def tripleOverlap (i j k : I) :
    ChosenPullback₃ (overlap Xᵢ f i j) (overlap Xᵢ f j k) (overlap Xᵢ f i k) :=
  let h₁₂ := overlap Xᵢ f i j
  let h₂₃ := overlap Xᵢ f j k
  let h₁₃ := overlap Xᵢ f i k
  let h := ChosenPullback.ofHasPullback h₁₂.p₂ h₂₃.p₁
  ChosenPullback₃.ofMiddle h₁₂ h₂₃ h₁₃ h
    { f := pullback.lift (h.p₁ ≫ h₁₂.p₁) (h.p₂ ≫ h₂₃.p₂) sorry
      f_p₁ := sorry
      f_p₂ := sorry
      f_p := sorry }

/-- The middle square of `tripleOverlap` is the pullback of the successive overlap
projections. -/
theorem tripleOverlap_chosenPullback (i j k : I) :
    (tripleOverlap Xᵢ f i j k).chosenPullback =
      ChosenPullback.ofHasPullback (overlap Xᵢ f i j).p₂ (overlap Xᵢ f j k).p₁ := sorry

/-- The property that every component in a chosen-overlap presentation is quasi-coherent. -/
abbrev chosenProperty
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :
    ObjectProperty ((Modules.descentPseudofunctor S).DescentData' sq sq₃) :=
  fun D ↦ ∀ i, (D.obj i).IsQuasicoherent

/-- Componentwise characterization of quasi-coherence in a chosen-overlap presentation. -/
theorem chosenProperty_iff
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (D : (Modules.descentPseudofunctor S).DescentData' sq sq₃) :
    chosenProperty Xᵢ f sq sq₃ D ↔ ∀ i, (D.obj i).IsQuasicoherent := sorry

/-- The chosen pairwise- and triple-overlap presentation of quasi-coherent descent data. -/
abbrev Chosen
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) :=
  (chosenProperty Xᵢ f sq sq₃).FullSubcategory

namespace Chosen

variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

/-- Regard chosen-overlap descent data with quasi-coherent components as a chosen
quasi-coherent descent datum. -/
def of (D : (Modules.descentPseudofunctor S).DescentData' sq sq₃)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) : Chosen Xᵢ f sq sq₃ :=
  ⟨D, hD⟩

/-- The underlying chosen-overlap descent datum of `of` is the supplied datum. -/
theorem of_obj (D : (Modules.descentPseudofunctor S).DescentData' sq sq₃)
    (hD : ∀ i, (D.obj i).IsQuasicoherent) :
    (of Xᵢ f sq sq₃ D hD).obj = D := sorry

/-- The source comparison morphism on a chosen pairwise overlap, as an isomorphism. -/
noncomputable def transitionIso (D : Chosen Xᵢ f sq sq₃) (i j : I) :=
  asIso (D.obj.hom i j)

/-- The forward map of `transitionIso` is the chosen descent comparison morphism. -/
theorem transitionIso_hom (D : Chosen Xᵢ f sq sq₃) (i j : I) :
    (transitionIso Xᵢ f sq sq₃ D i j).hom = D.obj.hom i j := sorry

/-- The comparison isomorphisms satisfy the cocycle condition on each chosen triple overlap. -/
theorem cocycle (D : Chosen Xᵢ f sq sq₃) (i j k : I) :
    Pseudofunctor.DescentData'.pullHom' D.obj.hom (sq₃ i j k).p
        (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom' D.obj.hom (sq₃ i j k).p
        (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom' D.obj.hom (sq₃ i j k).p
        (sq₃ i j k).p₁ (sq₃ i j k).p₃ := sorry

/-- A morphism of chosen descent data commutes with each pairwise comparison morphism. -/
theorem hom_compatibility {D E : Chosen Xᵢ f sq sq₃} (g : D ⟶ E) (i j : I) :
    ((Modules.descentPseudofunctor S).map (sq i j).p₁.op.toLoc).toFunctor.map (g.hom.hom i) ≫
        E.obj.hom i j =
      D.obj.hom i j ≫
        ((Modules.descentPseudofunctor S).map (sq i j).p₂.op.toLoc).toFunctor.map
          (g.hom.hom j) := sorry

/-- The canonical descent equivalence carries the chosen quasi-coherence property to the
canonical quasi-coherence property. -/
theorem inverseImage_descentProperty :
    (descentProperty Xᵢ f).inverseImage
        (Pseudofunctor.DescentData'.descentDataEquivalence
          (Modules.descentPseudofunctor S) sq sq₃).functor =
      chosenProperty Xᵢ f sq sq₃ := sorry

/-- The canonical equivalence between chosen-overlap and representation-independent
quasi-coherent descent data. -/
noncomputable def equivalence : Chosen Xᵢ f sq sq₃ ≌ DescentData Xᵢ f :=
  (Pseudofunctor.DescentData'.descentDataEquivalence
      (Modules.descentPseudofunctor S) sq sq₃).congrFullSubcategory
    (inverseImage_descentProperty Xᵢ f sq sq₃)

/-- The chosen-to-canonical equivalence retains every component object. -/
theorem equivalence_functor_obj_obj (D : Chosen Xᵢ f sq sq₃) (i : I) :
    ((equivalence Xᵢ f sq sq₃).functor.obj D).obj.obj i = D.obj.obj i := sorry

/-- The chosen-to-canonical equivalence retains every component of a morphism. -/
theorem equivalence_functor_map_hom {D E : Chosen Xᵢ f sq sq₃}
    (g : D ⟶ E) (i : I) :
    ((equivalence Xᵢ f sq sq₃).functor.map g).hom.hom i = g.hom.hom i := sorry

end Chosen

end DescentData

end AlgebraicGeometry.AlgebraicSpace.QCoh
