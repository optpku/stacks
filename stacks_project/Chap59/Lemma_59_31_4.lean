module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.31.4 (1): the support of a section of an abelian sheaf on the small étale
site is closed. -/
@[stacks 04FT] #check (AlgebraicGeometry.Scheme.Etale.isClosed_abelianSheafSectionSupport :
  ∀ {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)),
    IsClosed (abelianSheafSectionSupport F U σ : Set U.left))

/- Lemma 59.31.4 (2): the support of a sum of sections is contained in the union of
their supports. -/
@[stacks 04FT] #check (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionSupport_add_subset :
  ∀ {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ σ' : F.1.obj (op U)),
    (abelianSheafSectionSupport F U (σ + σ') : Set U.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left) ∪
        (abelianSheafSectionSupport F U σ' : Set U.left))

/- Lemma 59.31.4 (3): a morphism of abelian sheaves cannot enlarge the support of a
local section. -/
@[stacks 04FT] #check (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionSupport_map_subset :
  ∀ {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : S.Etale) (σ : F.1.obj (op U)),
    (abelianSheafSectionSupport G U (φ.hom.app (op U) σ) : Set U.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left))

/- Lemma 59.31.4 (4): the support of an abelian sheaf is the union of the images of
the supports of all its local sections. -/
@[stacks 04FT] #check (AlgebraicGeometry.Scheme.Etale.abelianSheafSupport_eq_iUnion_sectionSupport :
  ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}),
    abelianSheafSupport F =
      ⋃ (U : S.Etale) (σ : F.1.obj (op U)),
        U.hom.base '' (abelianSheafSectionSupport F U σ : Set U.left))

/- Lemma 59.31.4 (5): a surjective morphism of abelian sheaves gives the reverse
inclusion of supports. -/
@[stacks 04FT] #check (AlgebraicGeometry.Scheme.Etale.abelianSheafSupport_subset_of_epi :
  ∀ {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) [Epi φ],
    abelianSheafSupport G ⊆ abelianSheafSupport F)

/- Lemma 59.31.4 (6): an injective morphism of abelian sheaves gives an inclusion of
supports. -/
@[stacks 04FT] #check (AlgebraicGeometry.Scheme.Etale.abelianSheafSupport_subset_of_mono :
  ∀ {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) [Mono φ],
    abelianSheafSupport F ⊆ abelianSheafSupport G)

end AlgebraicGeometry.Scheme.Etale

end
