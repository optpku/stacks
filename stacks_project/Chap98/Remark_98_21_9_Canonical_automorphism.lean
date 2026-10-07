module

public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation
public import stacks_project.Chap98.Lemma_98_21_2_Functor
public import stacks_project.Chap98.Remark_98_21_4_Automorphisms_InfHom
public import stacks_project.Chap98.Remark_98_21_9_Canonical_automorphism_Kaehler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical automorphisms of infinitesimal deformations

For objects `x`, `y` over `Spec(A)` and a fibre morphism `α` over `Spec(B)`,
the two pullbacks of `α` along `B ⟶ B[Ω_{B/A}]` differ by an infinitesimal
automorphism of the trivial deformation of `x|_Spec(B)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} (v : A ⟶ B)

/-- The restriction `x|_Spec(B)` of a fibre object over `Spec(A)` along `A ⟶ B`. -/
def restrictObj (x : X.p.Fiber (Over.mk σA)) :
    X.p.Fiber (Over.mk (Spec.map v ≫ σA)) :=
  Chosen.reindexObj X.p (specOverHom v rfl) x

/-- `restrictObj v x` is selected reindexing of `x` along `specOverHom v`. -/
theorem restrictObj_eq (x : X.p.Fiber (Over.mk σA)) :
    restrictObj v x = Chosen.reindexObj X.p (specOverHom v rfl) x := sorry

/-- The two sections `B ⟶ B[Ω_{B/A}]` induce the same morphism
`Spec(B[Ω_{B/A}]) ⟶ Spec(A)`, since `d_{B/A}` vanishes on the image of `A`. -/
theorem specOverCan_comp_restrict :
    specOverCan v rfl ≫ specOverHom v rfl =
      specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl := sorry

variable (x y : X.p.Fiber (Over.mk σA))

/-- The pullback of `α` along the first-summand section `Spec(B[Ω_{B/A}]) ⟶ Spec(B)`. -/
def inlHomPullback (α : restrictObj v x ⟶ restrictObj v y) :
    trivialDeformation (restrictObj v x) (kaehlerObj v) ⟶
      trivialDeformation (restrictObj v y) (kaehlerObj v) :=
  Chosen.reindexMap X.p (specOverInl (Spec.map v ≫ σA) (kaehlerObj v)) α

/-- `inlHomPullback` is selected reindexing of `α` along `specOverInl`. -/
theorem inlHomPullback_eq (α : restrictObj v x ⟶ restrictObj v y) :
    inlHomPullback v x y α =
      Chosen.reindexMap X.p (specOverInl (Spec.map v ≫ σA) (kaehlerObj v)) α :=
  sorry

/-- The pullback of `α` along the canonical section `b ↦ (b, d_{B/A} b)`. -/
def canHomPullback (α : restrictObj v x ⟶ restrictObj v y) :
    Chosen.reindexObj X.p (specOverCan v rfl) (restrictObj v x) ⟶
      Chosen.reindexObj X.p (specOverCan v rfl) (restrictObj v y) :=
  Chosen.reindexMap X.p (specOverCan v rfl) α

/-- `canHomPullback` is selected reindexing of `α` along `specOverCan`. -/
theorem canHomPullback_eq (α : restrictObj v x ⟶ restrictObj v y) :
    canHomPullback v x y α = Chosen.reindexMap X.p (specOverCan v rfl) α := sorry

/-- Selected comparison of the two-step reindex of `x` along `inl` after `A ⟶ B`
with reindexing along the composite `Spec(B[Ω_{B/A}]) ⟶ Spec(A)`. -/
def reindexFromAInl :
    Chosen.reindexObj X.p
        (specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl) x ≅
      trivialDeformation (restrictObj v x) (kaehlerObj v) :=
  Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl)
    (specOverInl (Spec.map v ≫ σA) (kaehlerObj v))
    (specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl) rfl x

/-- The forward map of `reindexFromAInl` is the selected `inl`-composite comparison. -/
theorem reindexFromAInl_hom :
    (reindexFromAInl v x).hom =
      (Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl)
        (specOverInl (Spec.map v ≫ σA) (kaehlerObj v))
        (specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl) rfl x).hom :=
  sorry

/-- Selected comparison of the two-step reindex of `x` along `can` after `A ⟶ B`
with reindexing along the same composite `Spec(B[Ω_{B/A}]) ⟶ Spec(A)`. -/
def reindexFromACan :
    Chosen.reindexObj X.p
        (specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl) x ≅
      Chosen.reindexObj X.p (specOverCan v rfl) (restrictObj v x) :=
  Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl) (specOverCan v rfl)
    (specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl)
    (specOverCan_comp_restrict v) x

/-- The forward map of `reindexFromACan` is the selected `can`-composite comparison. -/
theorem reindexFromACan_hom :
    (reindexFromACan v x).hom =
      (Chosen.Reindex.specifiedCompIsoApp X.p (specOverHom v rfl) (specOverCan v rfl)
        (specOverInl (Spec.map v ≫ σA) (kaehlerObj v) ≫ specOverHom v rfl)
        (specOverCan_comp_restrict v) x).hom := sorry

/-- Fibre identification of the `can`-reindex of `x|_Spec(B)` with the trivial
deformation, using that `can` and `inl` agree over `Spec(A)`. -/
def canRestrictIso :
    Chosen.reindexObj X.p (specOverCan v rfl) (restrictObj v x) ≅
      trivialDeformation (restrictObj v x) (kaehlerObj v) :=
  (reindexFromACan v x).symm ≪≫ reindexFromAInl v x

/-- `canRestrictIso` is the composite of the two `Spec(A)`-level comparisons. -/
theorem canRestrictIso_hom :
    (canRestrictIso v x).hom =
      (reindexFromACan v x).inv ≫ (reindexFromAInl v x).hom := sorry

/-- Selected comparison identifying the `can`-reindex with the reindex along `τ` of
the trivial deformation, via `τ ∘ inl = can`. -/
def tauCompIso :
    Chosen.reindexObj X.p (specOverCan v rfl) (restrictObj v x) ≅
      Chosen.reindexObj X.p (specOverTau v rfl)
        (trivialDeformation (restrictObj v x) (kaehlerObj v)) :=
  Chosen.Reindex.specifiedCompIsoApp X.p
    (specOverInl (Spec.map v ≫ σA) (kaehlerObj v)) (specOverTau v rfl)
    (specOverCan v rfl) (specOverTau_comp_inl v rfl) (restrictObj v x)

/-- The forward map of `tauCompIso` is the selected `τ ∘ inl = can` comparison. -/
theorem tauCompIso_hom :
    (tauCompIso v x).hom =
      (Chosen.Reindex.specifiedCompIsoApp X.p
        (specOverInl (Spec.map v ≫ σA) (kaehlerObj v)) (specOverTau v rfl)
        (specOverCan v rfl) (specOverTau_comp_inl v rfl) (restrictObj v x)).hom :=
  sorry

/-- Fibre identification of the trivial deformation of `x|_Spec(B)` with its
reindex along `τ`. -/
def canTauIso :
    trivialDeformation (restrictObj v x) (kaehlerObj v) ≅
      Chosen.reindexObj X.p (specOverTau v rfl)
        (trivialDeformation (restrictObj v x) (kaehlerObj v)) :=
  (canRestrictIso v x).symm ≪≫ tauCompIso v x

/-- `canTauIso` is `canRestrictIso` followed by `tauCompIso`. -/
theorem canTauIso_hom :
    (canTauIso v x).hom = (canRestrictIso v x).inv ≫ (tauCompIso v x).hom := sorry

/-- Reindex of `α|_inl` along `τ`. In a strict cleavage this is the parallel
arrow `α_can` on the same trivial deformations. -/
def tauHomPullback (α : restrictObj v x ⟶ restrictObj v y) :
    Chosen.reindexObj X.p (specOverTau v rfl)
        (trivialDeformation (restrictObj v x) (kaehlerObj v)) ⟶
      Chosen.reindexObj X.p (specOverTau v rfl)
        (trivialDeformation (restrictObj v y) (kaehlerObj v)) :=
  Chosen.reindexMap X.p (specOverTau v rfl) (inlHomPullback v x y α)

/-- `tauHomPullback` is selected reindexing of `α|_inl` along `specOverTau`. -/
theorem tauHomPullback_eq (α : restrictObj v x ⟶ restrictObj v y) :
    tauHomPullback v x y α =
      Chosen.reindexMap X.p (specOverTau v rfl) (inlHomPullback v x y α) :=
  sorry

/-- The canonical pullback of `α`, as a parallel arrow to `α|_inl` between the
trivial deformations of `x|_Spec(B)` and `y|_Spec(B)`. It is `τ*(α|_inl)`,
transported along `canTauIso` so as to retain `d_{B/A}`. -/
def canHomOverTriv (α : restrictObj v x ⟶ restrictObj v y) :
    trivialDeformation (restrictObj v x) (kaehlerObj v) ⟶
      trivialDeformation (restrictObj v y) (kaehlerObj v) :=
  (canTauIso v x).hom ≫ tauHomPullback v x y α ≫ (canTauIso v y).inv

/-- `canHomOverTriv` is the conjugate of `tauHomPullback` by `canTauIso`. -/
theorem canHomOverTriv_eq (α : restrictObj v x ⟶ restrictObj v y) :
    canHomOverTriv v x y α =
      (canTauIso v x).hom ≫ tauHomPullback v x y α ≫ (canTauIso v y).inv :=
  sorry

/-- The underlying infinitesimal automorphism of the trivial deformation of
`x|_Spec(B)` measuring `α_can - α|_inl` by left fibre composition. -/
def canonicalAutArrow (α : restrictObj v x ⟶ restrictObj v y) :
    Aut (trivialDeformation (restrictObj v x) (kaehlerObj v)) where
  hom := canHomOverTriv v x y α ≫ inv (inlHomPullback v x y α)
  inv := inlHomPullback v x y α ≫ inv (canHomOverTriv v x y α)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Left fibre composition with `canonicalAutArrow` recovers the parallel
canonical pullback: `hom ≫ α|_inl = τ*(α|_inl)`. -/
theorem canonicalAutArrow_hom (α : restrictObj v x ⟶ restrictObj v y) :
    (canonicalAutArrow v x y α).hom =
      canHomOverTriv v x y α ≫ inv (inlHomPullback v x y α) := sorry

variable [IsLocallyNoetherian S] [HasStrongRimSchlessinger X]

/-- Remark 98.21.9 (Canonical automorphism). Let `S` be a locally Noetherian
scheme and let `X` be a category fibred in groupoids over `(Sch/S)_fppf`
satisfying (RS*). Let `A` be an `S`-algebra such that `Spec(A) ⟶ S` maps into
an affine open, and let `x`, `y` be objects of `X` over `Spec(A)`. For a ring
map `A ⟶ B` and a morphism `α : x|_Spec(B) ⟶ y|_Spec(B)` over `Spec(B)`, the
canonical automorphism `φ(x, y, α)` is the difference, in the sense of
Remark 98.21.4, of the pullbacks of `α` along the two sections
`B ⟶ B[Ω_{B/A}]` given by `b ↦ inl b + inr (d_{B/A} b)` and by first-summand
inclusion. It is an element of `Inf_{x|_Spec(B)}(Ω_{B/A})`, and depends on
`A`, `x`, `y`, `A ⟶ B` and `α`. -/
@[stacks 07YD]
def canonicalAut (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : restrictObj v x ⟶ restrictObj v y) :
    (infFunctor (restrictObj v x)).obj (kaehlerObj v) :=
  ⟨canonicalAutArrow v x y α, sorry⟩

/-- The underlying fibre automorphism of `canonicalAut` is `canonicalAutArrow`. -/
theorem canonicalAut_val (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : restrictObj v x ⟶ restrictObj v y) :
    (canonicalAut v x y h_mapsIntoAffineOpen α).val = canonicalAutArrow v x y α :=
  sorry

/-- Left fibre action of `canonicalAutArrow` on `α|_inl` recovers the parallel
canonical pullback `τ*(α|_inl)`. This is the `infHomLeftAct` equation of
Remark 98.21.4. -/
theorem canonicalAut_spec (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : restrictObj v x ⟶ restrictObj v y) :
    (canonicalAutArrow v x y α).hom ≫ inlHomPullback v x y α =
      canHomOverTriv v x y α := sorry

/-- The canonical automorphism restricts to the identity on `x|_Spec(B)`, i.e.
it lies in `Inf_{x|_Spec(B)}(Ω_{B/A})`. -/
theorem canonicalAut_restrict (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen)
    (α : restrictObj v x ⟶ restrictObj v y) :
    (canonicalAutArrow v x y α).hom.1 ≫
        Chosen.cartesianHom X.p (specOverInl (Spec.map v ≫ σA) (kaehlerObj v))
          (restrictObj v x) =
      Chosen.cartesianHom X.p (specOverInl (Spec.map v ≫ σA) (kaehlerObj v))
        (restrictObj v x) := sorry

/-- If `y = x` and `α` is the identity, the canonical automorphism is zero. -/
theorem canonicalAut_id (h_mapsIntoAffineOpen : σA.MapsIntoAffineOpen) :
    canonicalAut v x x h_mapsIntoAffineOpen (𝟙 (restrictObj v x)) = 0 := sorry

end AlgebraicGeometry.GroupoidsOver
