module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Artinian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.16.2: let `A` be an Artinian local ring and `f : Spec(A) ⟶ S` a morphism of
schemes. Then `f` is of finite type if and only if its composition with
`Spec(IsLocalRing.ResidueField A) ⟶ Spec(A)` is of finite type. -/
@[stacks 02HV] #check
  (AlgebraicGeometry.Scheme.Hom.finiteType_iff_finiteType_comp_residueField :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (f : Spec (CommRingCat.of A) ⟶ S),
      Scheme.Hom.FiniteType f ↔
        Scheme.Hom.FiniteType
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f))
