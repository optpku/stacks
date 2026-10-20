module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Cotangent

/-!
# Surjectivity criteria in the completed base category

A morphism in `CompleteLocalAlgCat Λ k` is surjective if and only if it is surjective
on cotangent spaces, if and only if it is surjective on the relative quotients by
`m_Λ · (-) + maximalIdeal ^ 2`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.4.2 (1): a morphism is surjective if and only if its induced cotangent map
is surjective. -/
@[stacks 06GZ] #check (CompleteLocalAlgCat.Hom.surjective_iff_mapAlgHom :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    Function.Surjective f.hom ↔
      Function.Surjective (IsLocalRing.CotangentSpace.mapAlgHom f.hom))

/- Lemma 90.4.2 (2): the ordinary cotangent map is surjective if and only if the
relative cotangent quotient map is surjective. -/
@[stacks 06GZ] #check (CompleteLocalAlgCat.Hom.mapAlgHom_surjective_iff_mapRelative :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    Function.Surjective (IsLocalRing.CotangentSpace.mapAlgHom f.hom) ↔
      Function.Surjective (CompleteLocalAlgCat.Hom.mapRelative f))

#check (CompleteLocalAlgCat.Hom.surjective_iff_mapRelative :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    Function.Surjective f.hom ↔ Function.Surjective (CompleteLocalAlgCat.Hom.mapRelative f))
