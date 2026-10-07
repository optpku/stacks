module

public import ReasLib.AlgebraicGeometry.Scheme.OpenImmersion
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

section

variable (X : RingedSpace.{u}) (U : Opens X)

/- Ringed-space restriction: if (X, 𝒪_X) is a ringed space and U ⊆ X is open, then the
restriction (U, 𝒪_X|_U) is a ringed space. Notation: 𝒪_U = 𝒪_X|_U. -/
#check (AlgebraicGeometry.SheafedSpace.restrict X U.isOpenEmbedding : RingedSpace.{u})

/- Ringed-space inclusion: there is a canonical morphism of ringed spaces
j : (U, 𝒪_U) ⟶ (X, 𝒪_X). -/
#check (AlgebraicGeometry.SheafedSpace.ofRestrict X U.isOpenEmbedding :
  AlgebraicGeometry.SheafedSpace.restrict X U.isOpenEmbedding ⟶ X)

end

section

variable (X : LocallyRingedSpace.{u}) (U : Opens X)

/- Locally ringed space restriction: if (X, 𝒪_X) is a locally ringed space, then so is (U, 𝒪_U). -/
#check (AlgebraicGeometry.LocallyRingedSpace.restrict X U.isOpenEmbedding :
  LocallyRingedSpace.{u})

/- Locally ringed space inclusion: the canonical inclusion is a morphism of locally ringed spaces. -/
#check (AlgebraicGeometry.LocallyRingedSpace.ofRestrict X U.isOpenEmbedding :
  AlgebraicGeometry.LocallyRingedSpace.restrict X U.isOpenEmbedding ⟶ X)

end

section

variable {X : Scheme.{u}} (U : X.Opens)

/- Open-subscheme construction: if (X, 𝒪_X) is a scheme, then so is (U, 𝒪_U). -/
#check (AlgebraicGeometry.Scheme.Opens.toScheme U : Scheme.{u})

/- Open-subscheme inclusion: the canonical inclusion is a morphism of schemes. -/
#check (AlgebraicGeometry.Scheme.Opens.ι U : U.toScheme ⟶ X)

/- Canonical open immersion: (U, 𝒪_U) is an open subscheme of (X, 𝒪_X), and the
canonical inclusion j is an open immersion. -/
#check (AlgebraicGeometry.IsOpenImmersion.ofRestrict X U.isOpenEmbedding :
  IsOpenImmersion U.ι)

end

/- Remark 111.33.6 (8): a morphism of schemes is an open immersion exactly when it
is isomorphic over its target to the inclusion of an open subscheme. -/
@[stacks 02EY] #check (AlgebraicGeometry.Scheme.Hom.isOpenImmersion_iff_exists_iso :
  ∀ {V X : Scheme.{u}} (f : V ⟶ X),
    IsOpenImmersion f ↔ ∃ (U : X.Opens) (e : V ≅ U.toScheme), e.hom ≫ U.ι = f)
