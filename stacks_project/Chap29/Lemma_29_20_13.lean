module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits

universe u

/- Lemma 29.20.13 (1): for a locally finite-type morphism, the quasi-finite locus after base
change is the inverse image of the original quasi-finite locus. -/
@[stacks 01TM] #check
  (AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_locus_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f],
      {x' : (pullback f g : Scheme) | (pullback.snd f g).QuasiFiniteAt x'} =
        (pullback.fst f g) ⁻¹' {x : X | f.QuasiFiniteAt x})

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/- Lemma 29.20.13 (2): base change preserves the conjunction of local finite type and local
quasi-finiteness. -/
@[stacks 01TM] #check
  (CategoryTheory.MorphismProperty.pullback_snd
      (P := (@AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)) f g :
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f) →
      LocallyOfFiniteType (pullback.snd f g) ∧
        LocallyQuasiFinite (pullback.snd f g))

end

/- Lemma 29.20.13 (3): base change preserves quasi-finiteness. -/
@[stacks 01TM] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.pullback_snd :
    ∀ {X S S' : Scheme.{u}} {f : X ⟶ S}, Scheme.Hom.QuasiFinite f →
      ∀ g : S' ⟶ S, Scheme.Hom.QuasiFinite (pullback.snd f g))
