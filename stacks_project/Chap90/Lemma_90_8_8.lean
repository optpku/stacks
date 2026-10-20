module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothEssentialSurjectivity
import StacksCheckRecall

/-!
# Essential surjectivity of smooth morphisms of cofibered groupoids

A smooth morphism of categories cofibered in groupoids over `C_Λ` that is
essentially surjective on residue fibres is essentially surjective, as is its
completion.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{v} F] [Category.{v} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]

/- Lemma 90.8.8 (1): a smooth morphism of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` that is essentially surjective on residue fibres is
essentially surjective. -/
@[stacks 06HN] #check (CategoryTheory.BasedFunctor.essSurj :
  ∀ (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) [BasedFunctor.IsSmooth φ]
    [(φ.fiberFunctor (ArtinianLocalAlgCat.residue Λ k)).EssSurj],
    φ.toFunctor.EssSurj)

/- Lemma 90.8.8 (2): the completion of a smooth morphism of categories cofibered in
groupoids over `ArtinianLocalAlgCat Λ k` that is essentially surjective on residue
fibres is essentially surjective. -/
@[stacks 06HN] #check (CategoryTheory.BasedFunctor.map_essSurj :
  ∀ (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) [BasedFunctor.IsSmooth φ]
    [(φ.fiberFunctor (ArtinianLocalAlgCat.residue Λ k)).EssSurj],
    (FormalObject.map φ).EssSurj)
