/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Involution
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
import Mathlib.Tactic.CrossRefAttribute

/-!
# The swap equivalence of explicit pseudo-pullbacks

Double-swap components assemble the canonical involutivity isomorphism. The resulting explicit
quasi-inverse is the single owner from which the bicategorical equivalence and its property
instance are derived.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace PseudoPullback

noncomputable section
/-- The base-component isomorphism of the explicit double-swap comparison is the identity. -/
noncomputable def swap.involution.baseIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    baseObj (((swap F G) ⋙ swap G F).obj P) ≅ baseObj P :=
  Iso.refl _

/-- The first-component isomorphism of the explicit double-swap comparison is the identity. -/
noncomputable def swap.involution.fstIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    fstObj (((swap F G) ⋙ swap G F).obj P) ≅ fstObj P :=
  Iso.refl _

/-- The second-component isomorphism of the explicit double-swap comparison is the identity. -/
noncomputable def swap.involution.sndIsoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    sndObj (((swap F G) ⋙ swap G F).obj P) ≅ sndObj P :=
  Iso.refl _

/-- The forward first-component identity of the double-swap comparison lies over its forward
base identity. -/
theorem swap.involution.fstIsoApp.isHomLift
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    X.p.IsHomLift (swap.involution.baseIsoApp F G P).hom
      (swap.involution.fstIsoApp F G P).hom := sorry

/-- The forward second-component identity of the double-swap comparison lies over its forward
base identity. -/
theorem swap.involution.sndIsoApp.isHomLift
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    Y.p.IsHomLift (swap.involution.baseIsoApp F G P).hom
      (swap.involution.sndIsoApp F G P).hom := sorry

/-- The identity components of the explicit double-swap comparison respect the twice-inverted
structural comparison. -/
theorem swap.involution.compatibility
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    CommSq
      (F.toFunctor.map (swap.involution.fstIsoApp F G P).hom)
      (comparison (((swap F G) ⋙ swap G F).obj P))
      (comparison P)
      (G.toFunctor.map (swap.involution.sndIsoApp F G P).hom) := sorry

/-- The objectwise isomorphism from double swap to the original pseudo-pullback object. -/
noncomputable def swap.involution.isoApp
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    ((swap F G) ⋙ swap G F).obj P ≅ P :=
  mkIso
    (swap.involution.baseIsoApp F G P)
    (swap.involution.fstIsoApp F G P)
    (swap.involution.sndIsoApp F G P)
    (hom_fst := swap.involution.fstIsoApp.isHomLift F G P)
    (hom_snd := swap.involution.sndIsoApp.isHomLift F G P)
    (swap.involution.compatibility F G P)

/-- The base component of the forward double-swap comparison is the identity base
isomorphism. -/
@[simp]
theorem swap.involution.isoApp.hom.base
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    baseMap (swap.involution.isoApp F G P).hom =
      (swap.involution.baseIsoApp F G P).hom := sorry

/-- The first component of the forward double-swap comparison is the identity first
isomorphism. -/
@[simp]
theorem swap.involution.isoApp.hom.fst
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    fstMap (swap.involution.isoApp F G P).hom =
      (swap.involution.fstIsoApp F G P).hom := sorry

/-- The second component of the forward double-swap comparison is the identity second
isomorphism. -/
@[simp]
theorem swap.involution.isoApp.hom.snd
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    sndMap (swap.involution.isoApp F G P).hom =
      (swap.involution.sndIsoApp F G P).hom := sorry

/-- The base component of the inverse double-swap comparison is the inverse identity base
isomorphism. -/
@[simp]
theorem swap.involution.isoApp.inv.base
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    baseMap (swap.involution.isoApp F G P).inv =
      (swap.involution.baseIsoApp F G P).inv := sorry

/-- The first component of the inverse double-swap comparison is the inverse identity first
isomorphism. -/
@[simp]
theorem swap.involution.isoApp.inv.fst
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    fstMap (swap.involution.isoApp F G P).inv =
      (swap.involution.fstIsoApp F G P).inv := sorry

/-- The second component of the inverse double-swap comparison is the inverse identity second
isomorphism. -/
@[simp]
theorem swap.involution.isoApp.inv.snd
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    sndMap (swap.involution.isoApp F G P).inv =
      (swap.involution.sndIsoApp F G P).inv := sorry

/-- The explicit double-swap comparison components are natural in pseudo-pullback morphisms. -/
theorem swap.involution.isoApp.naturality
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    ((swap F G) ⋙ swap G F).map φ ≫ (swap.involution.isoApp F G Q).hom =
      (swap.involution.isoApp F G P).hom ≫ φ := sorry

/-- Every forward component of the explicit double-swap comparison is vertical over the
identity. -/
theorem swap.involution.isoApp.isHomLift
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (PseudoPullback F G).p.IsHomLift
      (𝟙 ((PseudoPullback F G).p.obj P))
      (swap.involution.isoApp F G P).hom := sorry

/-- Canonical componentwise based isomorphism witnessing that swap is involutive. -/
@[stacks 0040 "involutivity isomorphism of the explicit pseudo-pullback swap"]
noncomputable def swap.involution.iso (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap F G ⋙ swap G F ≅ 𝟙 (PseudoPullback F G) :=
  BasedNatIso.ofComponents
    (swap.involution.isoApp F G)
    (fun φ ↦ swap.involution.isoApp.naturality F G φ)
    (swap.involution.isoApp.isHomLift F G)

/-- The forward component of the based double-swap isomorphism is the explicit objectwise
comparison. -/
@[simp]
theorem swap.involution.iso.hom.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.involution.iso F G).hom.toNatTrans.app P =
      (swap.involution.isoApp F G P).hom := sorry

/-- The inverse component of the based double-swap isomorphism is the inverse explicit
objectwise comparison. -/
@[simp]
theorem swap.involution.iso.inv.app
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    (swap.involution.iso F G).inv.toNatTrans.app P =
      (swap.involution.isoApp F G P).inv := sorry

/-- The explicit swap together with the reverse swap forms quasi-inverse data over `C`. -/
def swap.quasiInverse (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    QuasiInverse (swap F G) where
  inverse := swap G F
  unitIso := (swap.involution.iso F G).symm
  counitIso := swap.involution.iso G F

/-- The inverse in the explicit swap quasi-inverse data is the reverse swap. -/
@[simp]
theorem swap.quasiInverse.inverse (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.quasiInverse F G).inverse = swap G F := sorry

/-- The unit in the explicit swap quasi-inverse data is inverse double swap. -/
@[simp]
theorem swap.quasiInverse.unit (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.quasiInverse F G).unitIso = (swap.involution.iso F G).symm := sorry

/-- The counit in the explicit swap quasi-inverse data is double swap in the reverse order. -/
@[simp]
theorem swap.quasiInverse.counit (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.quasiInverse F G).counitIso = swap.involution.iso G F := sorry

/-- The canonical bicategorical equivalence exchanging the two legs of an explicit based
pseudo-pullback. Its inverse is the reverse swap; the supplied involutivity unit is retained and
the counit is canonically adjointified. -/
@[stacks 0040 "equivalence exchanging the legs of an explicit pseudo-pullback"]
noncomputable def swap.equivalence (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    PseudoPullback F G ≌ PseudoPullback G F :=
  (swap.quasiInverse F G).toEquivalencePreservingUnit

/-- The forward morphism of the based pseudo-pullback swap equivalence is the explicit swap. -/
@[simp]
theorem swap.equivalence.hom (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.equivalence F G).hom = swap F G := sorry

/-- The inverse morphism of the based pseudo-pullback swap equivalence is the reverse swap. -/
@[simp]
theorem swap.equivalence.inv (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.equivalence F G).inv = swap G F := sorry

/-- The unit of the based pseudo-pullback swap equivalence is the supplied double-swap
comparison in the reverse direction. -/
@[simp]
theorem swap.equivalence.unit (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.equivalence F G).unit = (swap.involution.iso F G).symm := sorry

/-- The counit of the based pseudo-pullback swap equivalence is the canonical adjointification
of the reverse double-swap comparison. -/
@[simp]
theorem swap.equivalence.counit (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap.equivalence F G).counit =
      Bicategory.adjointifyCounit
        (swap.involution.iso F G).symm (swap.involution.iso G F) := sorry

/-- Swapping the legs of an explicit based pseudo-pullback is an equivalence over the base. -/
instance swap.isEquivalence (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    (swap F G).IsEquivalence := sorry
/- Proof strategy: use `swap.quasiInverse F G` as the explicit witness. -/

/- Data audit: `swap.quasiInverse` explicitly stores the reverse swap and both involutivity
isomorphisms. `swap.equivalence` delegates bicategorical packaging to the generic
`BasedFunctor.QuasiInverse.toEquivalencePreservingUnit`; no inverse or coherence data are
reselected at this layer. -/
end

end PseudoPullback
end BasedCategory
end CategoryTheory
