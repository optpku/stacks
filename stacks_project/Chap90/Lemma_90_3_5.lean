module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Cotangent

/-!
# Surjectivity criteria in the base category

A morphism in `ArtinianLocalAlgCat Λ k` is surjective if and only if it is surjective
on cotangent spaces, if and only if it is surjective on the relative quotients by
`m_Λ · (-) + maximalIdeal ^ 2`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.3.5 (1): a morphism is surjective if and only if its induced cotangent map
is surjective. -/
@[stacks 06S3] #check (ArtinianLocalAlgCat.Hom.surjective_iff_mapAlgHom :
  ∀ {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B),
    Function.Surjective f.hom ↔
      Function.Surjective (IsLocalRing.CotangentSpace.mapAlgHom f.hom))

/- Lemma 90.3.5 (2): the ordinary cotangent map is surjective if and only if the
relative cotangent quotient map is surjective. -/
@[stacks 06S3] #check (ArtinianLocalAlgCat.Hom.mapAlgHom_surjective_iff_mapRelative :
  ∀ {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B),
    Function.Surjective (IsLocalRing.CotangentSpace.mapAlgHom f.hom) ↔
      Function.Surjective (ArtinianLocalAlgCat.Hom.mapRelative f))

#check (ArtinianLocalAlgCat.Hom.surjective_iff_mapRelative :
  ∀ {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B),
    Function.Surjective f.hom ↔ Function.Surjective (ArtinianLocalAlgCat.Hom.mapRelative f))
