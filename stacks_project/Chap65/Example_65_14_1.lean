module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Example 65.14.1 (1): the projections `s, t : R ⟶ U` are étale, and hence `j` is an étale
equivalence relation. -/
@[stacks 02Z1]
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.instIsEtaleEquivalenceRelation_preRelation :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)], (preRelation k).IsEtaleEquivalenceRelation)

/- Example 65.14.1 (2): the quotient `X = U / R` is an algebraic space by Theorem 65.10.5. -/
@[stacks 02Z1]
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.sheafOfPoints_spec :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
          uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj))

/- Example 65.14.1 (3): the relation scheme `R = Δ ⨿ Γ` is quasi-compact. -/
@[stacks 02Z1]
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.instCompactSpace_relationOver :
    ∀ (k : Type u) [Field k], CompactSpace (relationOver k).left)

/- Example 65.14.1 (4): since `R` is quasi-compact, `X` is quasi-separated. -/
@[stacks 02Z1]
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.quasiCompact_diag_sheafOfPoints :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj))

/- Example 65.14.1 (5): the morphism `j : R ⟶ U ×_k U` is not an immersion. -/
@[stacks 02Z1]
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.not_isImmersion_relationHom :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)], ¬ IsImmersion (relationHom k).left)

/- Example 65.14.1 (6): `X` is not locally separated because `j` is not an immersion. -/
@[stacks 02Z1]
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.not_isImmersion_diag_sheafOfPoints :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      ¬ (MorphismProperty.over (@IsImmersion)).relative uliftYoneda.{u + 1}
          (diag (sheafOfPoints k).obj))
