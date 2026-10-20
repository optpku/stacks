module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.FiniteNeighborhood
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.44.3: the canonical scheme-theoretic image of `h` supplies the closed
subscheme through `h.imageι`, while `h.toImage` supplies the factorization. Over
an open neighbourhood of `s`, this image is finite over the neighbourhood. -/
@[stacks 0AH8] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) (s : S)
      (hs : Set.Finite (h '' ((h ≫ g) ⁻¹' ({s} : Set S))))
      [AlgebraicGeometry.IsProper (h ≫ g)] [AlgebraicGeometry.IsSeparated g]
      [AlgebraicGeometry.LocallyOfFiniteType g],
      ∃ U : S.Opens, s ∈ U ∧ AlgebraicGeometry.IsFinite ((h.imageι ≫ g) ∣_ U))
