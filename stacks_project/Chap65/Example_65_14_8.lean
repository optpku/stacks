module

public import stacks_project.Chap65.Example_65_14_8_Action
public import stacks_project.Chap65.Example_65_14_8_Space
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Example 65.14.8 (1): for a characteristic-zero field, the lifted integers act on the
canonical affine line by translation. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.action :
    ∀ (k : Type u) [Field k] [CharZero k],
      AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.group →*
        Aut (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k))

/- Example 65.14.8 (2): a nonidentity translation fixes precisely the generic point. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.fixed_iff_genericPoint :
    ∀ (k : Type u) [Field k] [CharZero k]
      {n : AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.group},
      n ≠ 1 → ∀ u : (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left,
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.action k n).hom.left u = u ↔
          u = genericPoint (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.cover k).left)

/- Example 65.14.8 (3): characteristic zero gives an injective action on the generic residue
field. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.injective_genericResidueAut :
    ∀ (k : Type u) [Field k] [CharZero k],
      Function.Injective
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericResidueAut k))

/- Example 65.14.8 (4): the quotient is the fppf sheaf of the translation action. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.sheafOfPoints :
    ∀ (k : Type u) [Field k] [CharZero k],
      Sheaf
        (Scheme.fppfTopology.over
          (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k))
        (Type (u + 1)))
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.representableDiagonal_sheafOfPoints :
    ∀ (k : Type u) [Field k] [CharZero k],
      uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.sheafOfPoints k).obj))
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.atlas_etale :
    ∀ (k : Type u) [Field k] [CharZero k],
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.atlas k).hom)
#check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.atlas_locallySurjective :
    ∀ (k : Type u) [Field k] [CharZero k],
      Presheaf.IsLocallySurjective
        (Scheme.etaleTopology.over
          (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k))
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.atlas k).hom)

/- Example 65.14.8 (5): the generic point maps canonically to the quotient sheaf. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericHom :
    ∀ (k : Type u) [Field k] [CharZero k],
      AlgebraicGeometry.Scheme.PreRelation.specToQuotientHom
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.action k)
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericStructure k))

/- Example 65.14.8 (6): the generic point does not factor through a monomorphism from a field
spectrum. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.not_exists_mono_factor :
    ∀ (k : Type u) [Field k] [CharZero k],
      ¬ ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
          (ι : AlgebraicGeometry.Scheme.PreRelation.specToQuotientHom
            (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.action k)
            (AlgebraicGeometry.FieldExtension.specMap k L))
          (_ : CategoryTheory.Mono ι)
          (φ : AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericOver k ⟶
            AlgebraicGeometry.FieldExtension.specOver
              (AlgebraicGeometry.FieldExtension.specMap k L)),
          (Scheme.fppfTopology.over
            (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map φ ≫ ι =
            AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericHom k)

/- Example 65.14.8 (7): a monomorphic factorization has an isomorphic intervening field
spectrum. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.isIso_of_mono_factor :
    ∀ (k : Type u) [Field k] [CharZero k]
      {L : Type u} [Field L] [Algebra k L]
      (ι : AlgebraicGeometry.Scheme.PreRelation.specToQuotientHom
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.action k)
        (AlgebraicGeometry.FieldExtension.specMap k L))
      (φ : AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericOver k ⟶
        AlgebraicGeometry.FieldExtension.specOver
          (AlgebraicGeometry.FieldExtension.specMap k L))
      (_ : CategoryTheory.Mono ι)
      (_ : (Scheme.fppfTopology.over
        (AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map φ ≫ ι =
        AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericHom k),
      IsIso φ.left)

/- Example 65.14.8 (8): the generic-point morphism is not a monomorphism. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.not_mono_genericHom :
    ∀ (k : Type u) [Field k] [CharZero k],
      ¬ CategoryTheory.Mono
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericHom k))

/- Example 65.14.8 (9): the self-pullback is the coproduct indexed by the lifted integers. -/
@[stacks 02Z7] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.instIsIso_genericPullbackIso_inv :
    ∀ (k : Type u) [Field k] [CharZero k],
      IsIso
        (AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation.genericPullbackIso_inv k))
