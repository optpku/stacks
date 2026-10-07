module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.IntegralPushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u w

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]

/- Lemma 59.43.5 (1): for an integral morphism `f` (for example a finite morphism),
the small étale direct image `f_small,*` on sheaves of sets preserves surjections
(locally surjective morphisms). -/
@[stacks 04C2]
#check (AlgebraicGeometry.Scheme.SmallEtaleDirectImage.preservesLocallySurjective_of_isIntegralHom f :
  (Scheme.smallEtaleDirectImage f).PreservesLocallySurjective)

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Lemma 59.43.5 (2): for an integral morphism `f` (for example a finite morphism),
the small étale abelian direct image `f_small,*` preserves surjections. -/
@[stacks 04C2]
#check (AlgebraicGeometry.SmallAbelianPushforward.preservesEpimorphisms_of_isIntegralHom f :
  (AlgebraicGeometry.smallAbelianPushforward f).PreservesEpimorphisms)

/- Lemma 59.43.5 (3): for an integral morphism `f` (for example a finite morphism)
and any abelian sheaf `F` on `X` étale, the counit
`f_small^{-1} f_small,* F ⟶ F` is surjective. -/
@[stacks 04C2]
#check (AlgebraicGeometry.SmallAbelianPushforward.counit_epi_of_isIntegralHom f :
  ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
    Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F))

/- Lemma 59.43.5 (4): for an integral morphism `f` (for example a finite morphism),
the small étale abelian direct image `f_small,*` is faithful. -/
@[stacks 04C2]
#check (AlgebraicGeometry.SmallAbelianPushforward.faithful_of_isIntegralHom f :
  (AlgebraicGeometry.smallAbelianPushforward f).Faithful)

/- Lemma 59.43.5 (5): for an integral morphism `f` (for example a finite morphism),
the small étale abelian direct image `f_small,*` reflects injections. -/
@[stacks 04C2]
#check (AlgebraicGeometry.SmallAbelianPushforward.reflectsMonomorphisms_of_isIntegralHom f :
  (AlgebraicGeometry.smallAbelianPushforward f).ReflectsMonomorphisms)

/- Lemma 59.43.5 (6): for an integral morphism `f` (for example a finite morphism),
the small étale abelian direct image `f_small,*` reflects surjections. -/
@[stacks 04C2]
#check (AlgebraicGeometry.SmallAbelianPushforward.reflectsEpimorphisms_of_isIntegralHom f :
  (AlgebraicGeometry.smallAbelianPushforward f).ReflectsEpimorphisms)

/- Lemma 59.43.5 (7): for an integral morphism `f` (for example a finite morphism),
the small étale abelian direct image `f_small,*` is exact. -/
@[stacks 04C2]
#check (AlgebraicGeometry.SmallAbelianPushforward.exact_of_isIntegralHom f :
  exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{w})
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{w})
    (AlgebraicGeometry.smallAbelianPushforward f))
