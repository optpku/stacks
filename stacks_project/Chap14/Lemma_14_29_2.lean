module

public import ReasLib.Algebra.Homology.Homotopy.CylinderShortComplex
import StacksCheckRecall

/-!
@stack 01A3
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (A : ChainComplex C ℤ)

/- Lemma 14.29.2 (01A3), canonical data: the cylinder extension is represented by the bundled
short complex `A ⊞ A ⟶ A.cylinder ⟶ A⟦-1⟧`, together with its chosen degreewise splitting. -/
@[stacks 01A3 "Lemma 14.29.2, cylinder short complex"]
#check (cylinder.shortComplex A : ShortComplex (ChainComplex C ℤ))

/- Lemma 14.29.2 (01A3): the canonical cylinder sequence is short exact. -/
@[stacks 01A3 "Lemma 14.29.2, cylinder short exact sequence"]
#check (cylinder.shortComplex.shortExact A : (cylinder.shortComplex A).ShortExact)

@[stacks 01A3 "Lemma 14.29.2, cylinder degreewise splitting"]
#check (cylinder.splitting A :
  ShortComplex.DegreewiseSplitting (cylinder.shortComplex A))

/- Lemma 14.29.2 (01A3), boundary identification: the connecting map of the cylinder extension is
the shifted difference `(𝟙 A, -𝟙 A)⟦-1⟧'`. -/
@[stacks 01A3 "Lemma 14.29.2, cylinder boundary map"]
#check (cylinder.boundary_eq A :
  homOfDegreewiseSplit (cylinder.shortComplex A) (cylinder.splitting A) =
    (biprod.lift (𝟙 A) (-𝟙 A))⟦(-1 : ℤ)⟧')

end ChainComplex

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : ChainComplex C ℤ}
variable (ι : A ⊞ A ⟶ B) (ρ : B ⟶ D) (w : ι ≫ ρ = 0)
variable (hS : (ShortComplex.mk ι ρ w).ShortExact)
variable (s : ∀ n : ℤ, D.X n ⟶ B.X n)
variable (hs : ∀ n : ℤ, s n ≫ ρ.f n = 𝟙 (D.X n))
variable (f : D ⟶ A⟦(-1 : ℤ)⟧)
variable (hboundary :
  DegreewiseSplitting.BoundaryCommSq (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A) (𝟙 (A ⊞ A)) f)

/- Lemma 14.29.2 (01A3), canonical data: the splitting formula gives the distinguished morphism
to the cylinder short complex, identity on `A ⊞ A` and equal to `f` on the right term. -/
#check
  (DegreewiseSplitting.hom (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A) (𝟙 (A ⊞ A)) f hboundary :
    ShortComplex.mk ι ρ w ⟶ ChainComplex.cylinder.shortComplex A)

/- Its middle component is the explicit canonical lift assembled degreewise from the chosen
splittings. -/
#check
  (DegreewiseSplitting.hom.τ₂ (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A) (𝟙 (A ⊞ A)) f hboundary)

/- The canonical morphism respects the source and cylinder splittings in every degree. -/
#check
  (DegreewiseSplitting.hom.respects (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A) (𝟙 (A ⊞ A)) f hboundary)

/- Lemma 14.29.2 (01A3), library-facing classification: splitting-compatible morphisms are
equivalent to compatible maps on the two outer terms. -/
#check
  (DegreewiseSplitting.homEquiv (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A))

/- Lemma 14.29.2 (01A3), uniqueness: the generic universal property specializes directly to
the short exact sequence with its section-induced splitting. -/
@[stacks 01A3 "Lemma 14.29.2"]
#check
  (DegreewiseSplitting.hom.existsUnique (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A) (𝟙 (A ⊞ A)) f hboundary :
    ∃! φ : ShortComplex.mk ι ρ w ⟶ ChainComplex.cylinder.shortComplex A,
      φ.τ₁ = 𝟙 (A ⊞ A) ∧ φ.τ₃ = f ∧
        φ.RespectsDegreewiseSplittings (hS.splittingOfSection s hs)
          (ChainComplex.cylinder.splitting A))

/- The corresponding unbundled middle-map formulation is the same generic API specialized to the
chosen degreewise splitting. -/
#check
  (DegreewiseSplitting.middle.existsUnique (hS.splittingOfSection s hs)
    (ChainComplex.cylinder.splitting A) (𝟙 (A ⊞ A)) f hboundary)

end CategoryTheory.ShortComplex
