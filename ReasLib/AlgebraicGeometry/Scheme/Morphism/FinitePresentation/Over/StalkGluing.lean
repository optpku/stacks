/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Localization.Construction
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-presentation gluing over a stalk

This leaf packages the neighborhood index, punctured-stalk open, and categorical pullback used to
compare finite-presentation schemes near a point with gluing data over the open complement and the
local scheme.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The opposite ordered index of open neighborhoods `W` of `s` containing a fixed open `U`. -/
abbrev OpenNeighborhoodIndex (S : Scheme.{u}) (U : S.Opens) (s : S) : Type u :=
  ({ W : S.Opens // U ≤ W ∧ s ∈ (W : Set S) })ᵒᵖ

namespace OpenNeighborhoodIndex

/-- The underlying open subset of an open-neighborhood index object. -/
abbrev toOpen {S : Scheme.{u}} {U : S.Opens} {s : S}
    (W : OpenNeighborhoodIndex S U s) : S.Opens :=
  W.unop.1

end OpenNeighborhoodIndex

/-- The open `Spec(𝒪_{S,s}) ×_S U`, i.e. the intersection of the canonical stalk scheme with
`U`. -/
abbrev stalkOpenIntersection (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (Spec (S.presheaf.stalk s)).Opens :=
  (S.fromSpecStalk s) ⁻¹ᵁ U

/-- The category of finite-presentation gluing data over `U`, over the stalk scheme, and over their
intersection. -/
abbrev finitePresentationStalkGluingCategory
    (S : Scheme.{u}) (U : S.Opens) (s : S) : Type (u + 1) :=
  CategoricalPullback
    (FinitePresentationOver.baseChange ((S.fromSpecStalk s) ∣_ U))
    (FinitePresentationOver.baseChange ((stalkOpenIntersection S U s).ι))

namespace FinitePresentationOver.OpenNeighborhood

/-- The pseudofunctor of finite-presentation schemes over open neighborhoods of a point,
with transition functors given by base change along inclusions of neighborhoods. -/
noncomputable def pseudofunctor (S : Scheme.{u}) (U : S.Opens) (s : S) :
    LocallyDiscrete (OpenNeighborhoodIndex S U s) ⥤ᵖ Cat.{u} := by
  let Q : LocallyDiscrete Scheme.{u} ⥤ᵖ Bicategory.Adj Cat.{u} :=
    LocallyDiscrete.mkPseudofunctor
      (fun X ↦ Bicategory.Adj.mk (Cat.of (Over X)))
      (fun f ↦ Bicategory.Adj.Hom.mk (Over.mapPullbackAdj f).toCat)
      (fun X ↦ Bicategory.Adj.iso₂Mk
        (Cat.Hom.isoMk (Over.mapId X)) (Cat.Hom.isoMk Over.pullbackId.symm))
      (fun f g ↦ Bicategory.Adj.iso₂Mk
        (Cat.Hom.isoMk (Over.mapComp f g)) (Cat.Hom.isoMk (Over.pullbackComp f g).symm))
      (fun _ _ _ ↦ by
        apply Bicategory.Adj.hom₂_ext
        apply Cat.Hom₂.ext
        ext X
        apply Over.OverMorphism.ext
        rfl)
      (fun _ ↦ by
        apply Bicategory.Adj.hom₂_ext
        apply Cat.Hom₂.ext
        ext X
        apply Over.OverMorphism.ext
        rfl)
      (fun _ ↦ by
        apply Bicategory.Adj.hom₂_ext
        apply Cat.Hom₂.ext
        ext X
        apply Over.OverMorphism.ext
        rfl)
  let R : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u} :=
    LocallyDiscrete.mkPseudofunctor
      (fun X ↦ (Q.obj ⟨X.unop⟩).obj)
      (fun f ↦ (Q.map f.unop.toLoc).r)
      (fun X ↦ Bicategory.Adj.rIso (Q.mapId ⟨X.unop⟩))
      (fun f g ↦ Bicategory.Adj.rIso (Q.mapComp g.unop.toLoc f.unop.toLoc))
      (fun f g h ↦ by
        have H := (congrArg (fun k ↦ k.τr)
          (Q.map₂_associator h.unop.toLoc g.unop.toLoc f.unop.toLoc)).symm
        convert H using 1 <;> rfl)
      (fun f ↦ by
        have H := congrArg (fun k ↦ k.τr)
          (Q.map₂_right_unitor f.unop.toLoc)
        rw [← IsIso.inv_eq_inv]
        rw [IsIso.inv_comp, IsIso.inv_comp, Bicategory.inv_whiskerRight]
        simp only [unop_id, Quiver.Hom.id_toLoc, unop_comp,
          Quiver.Hom.comp_toLoc] at H ⊢
        rw [IsIso.inv_eq_of_hom_inv_id (λ_ (Q.map f.unop.toLoc).r).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapId _)).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapComp f.unop.toLoc (𝟙 _))).hom_inv_id]
        rw [inv_eqToHom]
        simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.whiskerLeft_τr,
          Bicategory.Adj.rightUnitor_hom_τr] at H
        convert H.symm using 1 <;> rfl)
      (fun f ↦ by
        have H := congrArg (fun k ↦ k.τr)
          (Q.map₂_left_unitor f.unop.toLoc)
        rw [← IsIso.inv_eq_inv]
        rw [IsIso.inv_comp, IsIso.inv_comp, Bicategory.inv_whiskerLeft]
        simp only [unop_id, Quiver.Hom.id_toLoc, unop_comp,
          Quiver.Hom.comp_toLoc] at H ⊢
        rw [IsIso.inv_eq_of_hom_inv_id (ρ_ (Q.map f.unop.toLoc).r).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapId _)).hom_inv_id]
        rw [IsIso.inv_eq_of_hom_inv_id
          (Bicategory.Adj.rIso (Q.mapComp (𝟙 _) f.unop.toLoc)).hom_inv_id]
        rw [inv_eqToHom]
        simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.whiskerRight_τr,
          Bicategory.Adj.leftUnitor_hom_τr] at H
        convert H.symm using 1 <;> rfl)
  let G : OpenNeighborhoodIndex S U s ⥤ Scheme.{u}ᵒᵖ :=
    { obj := fun W ↦ Opposite.op W.toOpen.toScheme
      map := fun f ↦ (S.homOfLE (leOfHom f.unop)).op
      map_id := fun W ↦ Quiver.Hom.unop_inj (by
        simpa using S.homOfLE_rfl W.toOpen)
      map_comp := fun f g ↦ Quiver.Hom.unop_inj (by
        simpa using (S.homOfLE_homOfLE (leOfHom g.unop) (leOfHom f.unop)).symm) }
  let F := G.toPseudofunctor.comp R
  let P : F.ObjectProperty :=
    { prop := fun W ↦ finitePresentationOverProperty W.as.toOpen.toScheme }
  -- Local instance justification (proof-local temporary data): P.fullsubcategory requires this proof-valued preservation argument through typeclass search and selects no mathematical data.
  letI : P.IsClosedUnderMapObj :=
    { map_obj := fun hX f ↦ FinitePresentationOver.baseChange_mem
        (S.homOfLE (leOfHom f.as.unop)) ⟨_, hX⟩ }
  exact P.fullsubcategory

/-- The morphisms in the Grothendieck construction whose component in the target fiber is an
isomorphism. -/
def transitionMorphism (S : Scheme.{u}) (U : S.Opens) (s : S) :
    MorphismProperty (Pseudofunctor.Grothendieck (pseudofunctor S U s)) :=
  fun _ _ f ↦ IsIso f.fiber

/-- The categorical colimit of finite-presentation schemes over open neighborhoods, modeled by
localizing the Grothendieck construction at the fiberwise-isomorphism transition morphisms. -/
abbrev Colimit (S : Scheme.{u}) (U : S.Opens) (s : S) : Type (u + 1) :=
  (transitionMorphism S U s).Localization

end FinitePresentationOver.OpenNeighborhood

/-- Finite-presentation schemes over open neighborhoods of a point have colimit equivalent to
finite-presentation gluing data over the fixed open, the stalk scheme, and their intersection. -/
@[stacks 0BQ5]
theorem finitePresentation_openNeighborhood_colimit_equivalence_stalkGluing
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) :
    Nonempty
      (FinitePresentationOver.OpenNeighborhood.Colimit S U s ≌
        finitePresentationStalkGluingCategory S U s) := sorry

/-- Finite-presentation schemes over a scheme are equivalent to compatible
finite-presentation schemes over the complement of a closed point and over its local scheme. -/
theorem finitePresentationOver_equivalence_stalkGluing
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hs : s ∈ closedPoints S)
    (hU : (U : Set S) = ({s} : Set S)ᶜ) :
    Nonempty
      (FinitePresentationOver S ≌
        finitePresentationStalkGluingCategory S U s) := sorry

/-- Pulling the complement of a closed point back to its local scheme gives the punctured spectrum
of the local ring. -/
theorem stalkOpenIntersection_eq_puncturedOpen
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ closedPoints X)
    (hU : (U : Set X) = ({x} : Set X)ᶜ) :
    stalkOpenIntersection X U x =
      PuncturedSpectrum.puncturedOpen (X.presheaf.stalk x) := sorry

/-- For a locally finitely presented target over a base scheme, a morphism from a scheme is
determined uniquely by its restrictions to the complement of a closed point and to the local
scheme at that point, provided the two restrictions agree on the canonical stalk-open
intersection. -/
theorem morphismsOverRestrictPuncturedLocalSpecBijective
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFinitePresentation pY]
    (x : X) (hx : x ∈ closedPoints X)
    (U : X.Opens) (hU : (U : Set X) = ({x} : Set X)ᶜ)
    [QuasiCompact U.ι] :
    Set.BijOn
      (fun g : {g : X ⟶ Y // g ≫ pY = pX} ↦
        (U.ι ≫ g.1, X.fromSpecStalk x ≫ g.1))
      Set.univ
      ({ab : (U.toScheme ⟶ Y) × ((Spec (CommRingCat.of (X.presheaf.stalk x))) ⟶ Y) |
          ab.1 ≫ pY = U.ι ≫ pX} ∩
        {ab | ab.2 ≫ pY = X.fromSpecStalk x ≫ pX} ∩
        {ab | (X.fromSpecStalk x ∣_ U) ≫ ab.1 =
          (stalkOpenIntersection X U x).ι ≫ ab.2}) := sorry

end AlgebraicGeometry
