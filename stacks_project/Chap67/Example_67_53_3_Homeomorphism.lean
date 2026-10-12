/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap65.Example_65_14_1_Space
public import stacks_project.Chap67.Remark_67_19_4_Morphism

/-!
# Universal closedness and universal homeomorphism of the affine-line involution

This module records that `x ↦ x²` is universally closed, that the composite of the
atlas with `toAffineLine` is representably universally closed, and that
`X ⟶ 𝔸¹_k` is a universal homeomorphism in the sense of Definition 67.53.2:
every algebraic-space base change of `toAffineLine` induces a homeomorphism on
underlying spaces, tested by pullback squares of representable étale
locally-surjective scheme atlases whose comparison is a homeomorphism of
quotient spaces as in `AlgebraicSpace.pointsIsHomeomorph` and `IsPointsTopology`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The squaring endomorphism of the affine line over a field is universally closed. -/
instance squareMap_universallyClosed (k : Type u) [Field k] :
    UniversallyClosed (squareMap k) := sorry

end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The atlas `𝔸¹_k ⟶ X` is étale relative to `uliftYoneda`. -/
theorem etale_atlas (k : Type u) [Field k] [NeZero (2 : k)] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom :=
  sorry

/-- The atlas `𝔸¹_k ⟶ X` is étale-locally surjective. -/
theorem locallySurjective_atlas (k : Type u) [Field k] [NeZero (2 : k)] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom :=
  sorry

/-- The composite of the atlas with `toAffineLine` is representably universally closed. -/
theorem universallyClosed_comp_atlas_toAffineLine (k : Type u) [Field k] :
    (MorphismProperty.over (@UniversallyClosed)).relative uliftYoneda.{u + 1}
      (atlas k ≫ toAffineLine k).hom := sorry

/-- A morphism of Type `(u+1)` fppf sheaves over `Spec k` is a universal homeomorphism
in the sense of Definition 67.53.2: for every Type `(u+1)` fppf sheaf `Z` over
`Spec k` with representable diagonal and a representable étale locally-surjective
scheme atlas, every `IsPullback` of `f` along `Z ⟶ Y` has projection inducing a
homeomorphism on underlying spaces. This is tested by pullback squares of those
atlases, matching `AlgebraicSpace.pointsIsHomeomorph` and `IsPointsTopology`: the
induced comparison is a homeomorphism of the quotient spaces of the atlas
underlying spaces, not `Topology.IsQuotientMap` of every commuting scheme map. -/
def isUniversalHomeomorphism {k : Type u} [Field k]
    {X Y : Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1))} (f : X ⟶ Y) : Prop :=
  ∀ {Z P : Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1))}
    {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
    uliftYoneda.{u + 1}.relativelyRepresentable (diag Z.obj) →
    (∃ (V : Over (base k)) (q : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj V ⟶ Z),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) q.hom) →
    IsPullback pZ pX g f →
    ∀ {U V W : Over (base k)} (p : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶ P)
      (q : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj V ⟶ Z) (σ : W ⟶ U) (φ : W ⟶ V),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom →
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) p.hom →
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom →
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) q.hom →
      IsPullback ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map φ)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map σ) q (p ≫ pZ) →
      ∀ {RW RV : Over (base k)} (sW tW : RW ⟶ W) (sV tV : RV ⟶ V),
        IsPullback ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map sW)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map tW)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map σ ≫ p)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map σ ≫ p) →
        IsPullback ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map sV)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map tV) q q →
        let rW := fun x y : W.left ↦ ∃ r : RW.left, sW.left r = x ∧ tW.left r = y
        let rV := fun x y : V.left ↦ ∃ r : RV.left, sV.left r = x ∧ tV.left r = y
        (∀ x y, rW x y ↔ rV (φ.left x) (φ.left y)) ∧
          (∀ y, ∃ x, rV (φ.left x) y) ∧
            ∀ s : Set V.left, (∀ y y', rV y y' → (y ∈ s ↔ y' ∈ s)) →
              (IsOpen s ↔ IsOpen (φ.left ⁻¹' s))

/-- Universal homeomorphism means every algebraic-space base change of `f`, in the
Type `(u+1)` fppf sheaf encoding, induces a homeomorphism on underlying spaces,
tested by pullback squares of representable étale locally-surjective scheme
atlases whose comparison is a homeomorphism of quotient spaces. -/
theorem isUniversalHomeomorphism_iff {k : Type u} [Field k]
    {X Y : Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1))} (f : X ⟶ Y) :
    isUniversalHomeomorphism f ↔
      ∀ (Z P : Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)))
        (g : Z ⟶ Y) (pZ : P ⟶ Z) (pX : P ⟶ X),
        uliftYoneda.{u + 1}.relativelyRepresentable (diag Z.obj) →
        (∃ (V : Over (base k)) (q : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj V ⟶ Z),
          (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) q.hom) →
        IsPullback pZ pX g f →
        ∀ (U V W : Over (base k)) (p : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶ P)
          (q : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj V ⟶ Z) (σ : W ⟶ U) (φ : W ⟶ V),
          (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom →
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) p.hom →
          (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom →
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) q.hom →
          IsPullback ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map φ)
            ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map σ) q (p ≫ pZ) →
          ∀ (RW RV : Over (base k)) (sW tW : RW ⟶ W) (sV tV : RV ⟶ V),
            IsPullback ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map sW)
              ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map tW)
              ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map σ ≫ p)
              ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map σ ≫ p) →
            IsPullback ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map sV)
              ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map tV) q q →
            let rW := fun x y : W.left ↦ ∃ r : RW.left, sW.left r = x ∧ tW.left r = y
            let rV := fun x y : V.left ↦ ∃ r : RV.left, sV.left r = x ∧ tV.left r = y
            (∀ x y, rW x y ↔ rV (φ.left x) (φ.left y)) ∧
              (∀ y, ∃ x, rV (φ.left x) y) ∧
                ∀ s : Set V.left, (∀ y y', rV y y' → (y ∈ s ↔ y' ∈ s)) →
                  (IsOpen s ↔ IsOpen (φ.left ⁻¹' s)) :=
  sorry

/-- The morphism `X ⟶ 𝔸¹_k` is a universal homeomorphism in the sense of
Definition 67.53.2. -/
theorem universalHomeomorphism_toAffineLine (k : Type u) [Field k] [NeZero (2 : k)] :
    isUniversalHomeomorphism (toAffineLine k) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
