module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Universal homeomorphisms of universe-raised fppf sheaves

Universal homeomorphisms are tested after algebraic-space base change by the
kernel-pair relations and saturated open sets of representable étale atlases.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Sheaf

/-- A morphism of universe-raised fppf sheaves over a scheme is a universal
homeomorphism if every algebraic-space base change induces a homeomorphism of
underlying spaces. The criterion uses pullback squares of representable étale
locally-surjective scheme atlases: the comparison preserves and reflects the
kernel-pair relations, is surjective on their equivalence classes, and preserves
and reflects openness of saturated subsets. -/
def isUniversalHomeomorphism {S : Scheme.{u}}
    {X Y : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))} (f : X ⟶ Y) : Prop :=
  ∀ {Z P : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
    uliftYoneda.{u + 1}.relativelyRepresentable (diag Z.obj) →
    (∃ (V : Over S) (q : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj V ⟶ Z),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q.hom) →
    IsPullback pZ pX g f →
    ∀ {U V W : Over S} (p : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj U ⟶ P)
      (q : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj V ⟶ Z) (σ : W ⟶ U) (φ : W ⟶ V),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom →
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p.hom →
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom →
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q.hom →
      IsPullback ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map φ)
        ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map σ) q (p ≫ pZ) →
      ∀ {RW RV : Over S} (sW tW : RW ⟶ W) (sV tV : RV ⟶ V),
        IsPullback ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map sW)
          ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map tW)
          ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map σ ≫ p)
          ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map σ ≫ p) →
        IsPullback ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map sV)
          ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map tV) q q →
        let rW := fun x y : W.left ↦ ∃ r : RW.left, sW.left r = x ∧ tW.left r = y
        let rV := fun x y : V.left ↦ ∃ r : RV.left, sV.left r = x ∧ tV.left r = y
        (∀ x y, rW x y ↔ rV (φ.left x) (φ.left y)) ∧
          (∀ y, ∃ x, rV (φ.left x) y) ∧
            ∀ s : Set V.left, (∀ y y', rV y y' → (y ∈ s ↔ y' ∈ s)) →
              (IsOpen s ↔ IsOpen (φ.left ⁻¹' s))

/-- A universal homeomorphism of universe-raised fppf sheaves is characterized by
the kernel-pair relations, surjectivity on equivalence classes, and saturated-open
comparison for every representable étale atlas after algebraic-space base change. -/
theorem isUniversalHomeomorphism_iff {S : Scheme.{u}}
    {X Y : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))} (f : X ⟶ Y) :
    isUniversalHomeomorphism f ↔
      ∀ (Z P : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
        (g : Z ⟶ Y) (pZ : P ⟶ Z) (pX : P ⟶ X),
        uliftYoneda.{u + 1}.relativelyRepresentable (diag Z.obj) →
        (∃ (V : Over S) (q : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj V ⟶ Z),
          (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q.hom) →
        IsPullback pZ pX g f →
        ∀ (U V W : Over S) (p : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj U ⟶ P)
          (q : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj V ⟶ Z) (σ : W ⟶ U) (φ : W ⟶ V),
          (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom →
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p.hom →
          (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} q.hom →
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q.hom →
          IsPullback ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map φ)
            ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map σ) q (p ≫ pZ) →
          ∀ (RW RV : Over S) (sW tW : RW ⟶ W) (sV tV : RV ⟶ V),
            IsPullback ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map sW)
              ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map tW)
              ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map σ ≫ p)
              ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map σ ≫ p) →
            IsPullback ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map sV)
              ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map tV) q q →
            let rW := fun x y : W.left ↦ ∃ r : RW.left, sW.left r = x ∧ tW.left r = y
            let rV := fun x y : V.left ↦ ∃ r : RV.left, sV.left r = x ∧ tV.left r = y
            (∀ x y, rW x y ↔ rV (φ.left x) (φ.left y)) ∧
              (∀ y, ∃ x, rV (φ.left x) y) ∧
                ∀ s : Set V.left, (∀ y y', rV y y' → (y ∈ s ↔ y' ∈ s)) →
                  (IsOpen s ↔ IsOpen (φ.left ⁻¹' s)) :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Sheaf
